# READ-B: tensor foundations and the character interface (paper §2, (4.3)–(4.4))

Reader B. Scope is paper lines 70–141 (§2: Def 2.1, the semiring S, rank (2.1), T_n (2.2),
Lemma 2.2's statement, §2.1 (2.3)–(2.4), §2.2 Lemma 2.3) and 242–280 ((4.3)–(4.5), the six
permuted characters). Every file:line below was read with Read/`cat -n`/`sed -n`.
Path prefix `MM/` = `/home/user/openai-math/repo/lean/OAI/LinearAlgebra/MatrixMultiplication/`.

## 1. Files read

Read whole, in import order:

| file | lines |
|---|---|
| MM/Tensor/ComplexTensor.lean | 315 |
| MM/Tensor/ComplexTensorRestrictionComposition.lean | 206 |
| MM/Tensor/ComplexTensorBatching.lean | 97 |
| MM/Tensor/ComplexMatrixTensor.lean | 109 |
| MM/Tensor/ComplexTensorFlattening.lean | 70 |
| MM/Tensor/ComplexTensorSymmetrization.lean | 273 |
| MM/Tensor/ComplexDotPairing.lean | 33 |
| MM/Tensor/ComplexPairingMatrixTensor.lean | 143 |
| MM/Tensor/ComplexSeparatedTensorDecomposition.lean | 308 |
| MM/Tensor/ComplexLocalMaps.lean | 199 |
| MM/Tensor/ComplexGroupTensor.lean | 44 |
| MM/Tensor/ComplexSharedAuxiliaryBank.lean | 73 |
| MM/Tensor/ComplexFactorialLogBounds.lean | 152 |
| MM/AuxiliarySeparation/Character/Basic.lean | 158 |
| MM/AuxiliarySeparation/Tensor/DirectSum.lean | 139 |
| MM/AuxiliarySeparation/Tensor/Semiring.lean | 541 |
| MM/AuxiliarySeparation/Tensor/DirectSumClass.lean | 75 |
| MM/AuxiliarySeparation/Tensor/Scalar.lean | 140 |
| MM/AuxiliarySeparation/Tensor/CharacterBounds.lean | 220 |
| MM/AuxiliarySeparation/Tensor/BinaryCharacter.lean | 53 |
| MM/AuxiliarySeparation/Tensor/Characters.lean | 178 |
| MM/AuxiliarySeparation/Tensor/SixfoldProductBounds.lean | 111 |
| MM/AuxiliarySeparation/Tensor/SupportExtension.lean | 83 |
| MM/AuxiliarySeparation/Tensor/SharedPadding.lean | 147 |
| MM/AuxiliarySeparation/Tensor/TagInequality.lean | 222 |
| MM/AuxiliarySeparation/Character/Dot.lean | 175 |
| MM/AuxiliarySeparation/Character/Degeneration.lean | 165 |
| MM/AuxiliarySeparation/Character/Symmetrization.lean | 120 |
| MM/AuxiliarySeparation/Character/Permutation.lean | 116 |
| MM/AuxiliarySeparation/Character/FiniteSeparation.lean | 101 |
| MM/AuxiliarySeparation/Character/Existence.lean | 49 (statement only, per assignment) |

AuxiliarySeparation/Tensor/ total = 1,909 lines (wc confirmed: 53+220+178+139+75+140+541+147+111+83+222).

Additionally read whole because my questions' proofs live there (not assigned to me, read
for Q4/Q5): MM/AuxiliarySeparation/Growth/MultiplicativePower.lean (159),
MM/AuxiliarySeparation/Growth/PolynomialOverhead.lean (97),
MM/AuxiliarySeparation/Polynomial/Interpolation.lean (204),
MM/Polynomial/ComplexPolynomialApproximation.lean (182).

Partially read / grepped only: MM/ComplexArithmetic/Complexity.lean:125–150 (`matrixMultiplication`,
`AdmissibleExponent`, `omega`); MM/AuxiliarySeparation/Arithmetic/RankExponent.lean:20–48,138–150
(`exactRank`, `exactRankExponent`); MM/Polynomial/ComplexPolynomialDegenerationComposition.lean:80–140
(`PolynomialRestrictionDegeneration`); MM/AuxiliarySeparation/Convolution/Symmetry.lean:70–90
(`meanExponent`); MM/AuxiliarySeparation/Polynomial/Inequalities.lean:105–121 (the `0 < t` split);
MM/AuxiliarySeparation/Convolution/Basic.lean:24–25 (`convolution`);
MM/AuxiliarySeparation/Separation/Basic.lean:46–48,169–172,332–344 (`sharedFirstTensor`,
`separationTarget`, its direct-sum identity); MM/Separation/ComplexFiniteSeparation.lean:16–18
(`separatedTensor`).

## 2. Argument reconstruction (Lean chain → paper)

Objects (all in `MatrixMultiplication.Foundation.Tensor` unless noted):

1. `Tensor K X Y Z := X → Y → Z → K` (ComplexTensor.lean:16). A coefficient array of a trilinear
   form; finiteness comes from `[Fintype _]` hypotheses on each use. = paper "finite trilinear form".
2. `restrict A B C T x' y' z' = Σ_{x,y,z} A x' x · B y' y · C z' z · T x y z`
   (ComplexTensor.lean:31–35). A, B, C are arbitrary complex matrices X'×X etc., i.e. an
   independent linear substitution on each leg. `IsRestriction T S := ∃ A B C, T = restrict A B C S`
   (Semiring.lean:32–34), and the order on S is `T ≤ S ↔ IsRestriction T S` (Semiring.lean:143).
   = paper "A ≥ B iff B is a restriction of A". Composition: `restrict_restrict`
   (RestrictionComposition.lean:63) gives transitivity.
3. `product T S (x,u)(y,v)(z,w) = T x y z · S u v w` (ComplexTensor.lean:41–43): Kronecker product
   with legs paired. `directSum (T : ι → Tensor X Y Z)` is nonzero only when the block label agrees
   on ALL three legs (ComplexTensor.lean:45–47); binary `sumTensor` on `X ⊕ U` etc. likewise
   (DirectSum.lean:22–26). Both are the paper's full direct sum.
4. `matrixMultiplication a b c : Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a)`,
   coefficient 1 iff x=(i,j), y=(j,k), z=(k,i) (Complexity.lean:137–139) — Σ x_ij y_jk z_ki = T_n
   of (2.2) for a=b=c=n. `= matrixCoefficients (Fin a) (Fin b) (Fin c)` by `rfl`
   (ComplexMatrixTensor.lean:91–92).
5. `rankOne a b c = a x · b y · c z` (ComplexTensor.lean:24–25) and
   `RankAtMost T r := ∃ a b c : Fin r → …, T = Σ_i rankOne (a i) (b i) (c i)` (:27–29) — sum of r
   outer products with arbitrary complex vectors. `exactRank = Nat.find` of that
   (RankExponent.lean:36–39); `exactRankExponent = sInf {log_n R(T_n) : n ≥ 2}`
   (RankExponent.lean:142–146) = ν of (2.2).

Semiring S (paper §2, first paragraph):

6. `FiniteTensor` = (nx, ny, nz, coeff on Fin nx × Fin ny × Fin nz) (Semiring.lean:126–130);
   `TensorClass := Antisymmetrization FiniteTensor (≤)` (Semiring.lean:174), i.e. classes modulo
   mutual restriction. `classOf` sends a tensor on arbitrary finite types to its Fin presentation
   (Semiring.lean:187–188); `classOf_le_iff` (:190) and `classOf_eq_iff` (:196) show order and
   equality are restriction / mutual restriction regardless of presentation.
7. `+` = class of `sumTensor`, `*` = class of `product` (Semiring.lean:223–232), well-defined by
   `product_mono`/`sum_mono` (:162–168). `CommSemiring TensorClass` (Semiring.lean:367–380),
   with all axioms proved by explicit coordinate permutations
   (`sumTensor_assoc/comm/empty_right`, `tensorProduct_assoc/comm/one_right`, `product_sumTensor`,
   DirectSum.lean:50–135). 0 = zero tensor on Empty, 1 = scalar xyz on PUnit.
   `IsOrderedRing TensorClass` and `mul_mono`/`add_mono` (Semiring.lean:382–422) = "restriction
   induces an order compatible with both operations".
8. Naturals: `classOf (scalarTensor r) = (r : TensorClass)` (Scalar.lean:147), so m = ⊕ of m copies
   of 1; `classOf T ≤ r ↔ RankAtMost T r` (Scalar.lean:171) = paper's definition of R(A) as the least
   m with m ≥ A. `le_rank` (Scalar.lean:183), `one_le_of_ne_zero` (Semiring.lean:530) = (2.1).
   `rank_mono`, `rank_mul_le` (Semiring.lean:437,442). `matrixClass_mul` (Semiring.lean:465) =
   "reindexing identifies T_n T_m with T_nm". `classOf_directSum` (DirectSumClass.lean:47)
   = ι-indexed direct sums map to sums in S.

Characters (Def 2.1):

9. `structure Character` (Character/Basic.lean:35–55): `value` on tensors over finite types in
   `Type`, real-valued, with `nonneg`, `map_zero`, `map_one : value unitTensor = 1` where
   `unitTensor = fun _ _ _ => 1` on PUnit (Basic.lean:24) = the scalar tensor xyz,
   `map_directSum` over an arbitrary finite ι with arbitrary `DecidableEq`, `map_product`,
   `monotone : value (restrict A B C T) ≤ value T`.
10. `tensorClassHomEquiv : Character ≃ {φ : TensorClass →+* ℝ // Monotone φ}`
    (Tensor/Characters.lean:166–170). Descent uses `monotone` both ways
    (`valueOnTensorClass`, Characters.lean:30–39); additivity on DIFFERENT-shaped summands is
    DERIVED, not assumed (`value_sumTensor`, BinaryCharacter.lean:242, via zero-padding
    `value_dependentDirectSum`, CharacterBounds.lean:203). Nonnegativity of a monotone ring hom
    follows from 0 ≤ T (Characters.lean:113–115). So the Lean interface is EXACTLY Def 2.1
    (a monotone semiring hom S → ℝ; ℝ≥0-valuedness is automatic).
11. Consequences: `value_reindex` (Basic.lean:73), `value_eq_of_mutual_restriction` (:85),
    `value_scalarTensor : λ(r) = r` (:99), `value_le_rank : λ(T) ≤ r` if `RankAtMost T r`
    (:120), `one_le_value` for T ≠ 0 (:127). = paper's "λ(m)=m, 1 ≤ λ(A) ≤ R(A)".
12. Lemma 2.2 statement: `exists_detecting_character (hd : 2 ≤ d) (hk : k < d^ν) :
    ∃ χ, k ≤ χ.value (matrixMultiplication d d d)` (Existence.lean:25–27). Matches the paper
    exactly (ν = `exactRankExponent`). Proof not reviewed (reader C); it builds a monotone ring hom
    on `TensorClass` and converts with `ofTensorClassHom` (Existence.lean:39–43).

§2.1 dot products:

13. `dotPairing U : Tensor U U Unit`, 1 iff i = j (ComplexDotPairing.lean:16–17) = z·Σ x_i y_i =
    paper B_Z(m). `cyclic T y z x = T x y z` (ComplexTensorSymmetrization.lean:14–15).
    `cyclic (dotPairing)` : legs (Fin m, Unit, Fin m) = y·Σ x_i z_i = B_Y(m);
    `cyclic (cyclic dotPairing)` : legs (Unit, Fin m, Fin m) = x·Σ y_i z_i = B_X(m).
14. `cyclicCharacter` (Dot.lean:29–52) = χ∘cyclic, proved to be a Character.
    `pZ := log χ(dotPairing (Fin 2)) / log 2` (Dot.lean:107–108); `pY := χ.cyclicCharacter.pZ`,
    `pX := χ.cyclicCharacter.cyclicCharacter.pZ` (:111,114). Unfolding, pY = log₂ χ(B_Y(2)) and
    pX = log₂ χ(B_X(2)). So p_X = log₂ f(2), exactly the paper's definition.
15. f(m) = χ(dotPairing (Fin m)): positive (`value_dotPairing_pos`, Dot.lean:74, from
    `one_le_value`), ≤ m (`value_dotPairing_le`, :78, rank ≤ m), monotone (`value_dotPairing_mono`,
    :82, pullback along Fin.castLE), multiplicative (`value_dotPairing_mul`, :92, explicit reindex
    finProdFinEquiv of the product). `positiveMultiplicative_eq_rpow`
    (Growth/MultiplicativePower.lean:132) then gives f(m) = m^{log f(2)/log 2}. Its proof
    (`positiveMultiplicative_log_error_bounds`, :62–94) takes ℓ with 2^ℓ ≤ n^k < 2^{ℓ+1}
    (`exists_nat_pow_near`), transfers to f via monotonicity + multiplicativity, and shows
    k·(log f(n)·log 2 − log n·log f(2)) is bounded by a constant for all k, hence zero
    (`eq_of_nat_mul_sub_bounded`, :98). This is the paper's sandwich argument verbatim.
    `value_dotPairing` (Dot.lean:129), and the B_Y/B_X versions (:137,:142) via the cyclic characters.
16. `pZ_nonneg`, `pZ_le_one` (Dot.lean:116–122), and the same for pY, pX (:124–127): p ∈ [0,1].
17. (2.4): `pairingTriple A B C := dotPairing B ⊗ cyclic(dotPairing A) ⊗ cyclic²(dotPairing C)`
    (ComplexPairingMatrixTensor.lean:99–102) and `pairingTriple_matrixCoefficients`
    (:124–135) is an EXPLICIT pullback along three Equivs to `matrixCoefficients A B C`.
    Hence `value_matrixCoefficients : χ(T(a,b,c)) = b^{pZ} a^{pY} c^{pX}` (Dot.lean:148–153) and
    `value_matrixMultiplication : χ(T_m) = m^{pX+pY+pZ}` (Dot.lean:165–169). Index bookkeeping:
    the index shared by x,y (b) is a B_Z-type pairing, the one shared by x,z (a) a B_Y-type, the one
    shared by y,z (c) a B_X-type — consistent with the paper's monomials x_bc y_ac z_ab.
18. t > 0: NOT proved. `meanExponent := (pX+pY+pZ)/3` (Convolution/Symmetry.lean:76), only
    `meanExponent_nonneg`/`_le_one` (:78–87). The headline consumer
    `meanExponent_le_three_quarters` (Polynomial/Inequalities.lean:110–115) case-splits on
    `0 < t`; the `t ≤ 0` branch is closed by `linarith`. See Escalation E2 (resolved, harmless).

§2.2 degenerations, Lemma 2.3:

19. Lean's A ⇝ B is `PolynomialRestrictionDegeneration T U k Lx Ly Lz`
    (ComplexPolynomialDegenerationComposition.lean:94–107): three polynomial matrices
    `leftMap : X' → X → ℂ[ε]` etc. of degrees ≤ Lx, Ly, Lz such that the polynomial tensor
    `restrict leftMap middleMap rightMap (C ∘ T)` has all coefficients below ε^k zero and the
    ε^k coefficient equal to U. This is Strassen's algebraic degeneration with polynomial
    substitutions. It CONTAINS the paper's weight procedure (after shifting each leg's weights to
    be ≥ 0, which shifts k), so it is at least as general; see E3.
20. `value_scale_le` (Degeneration.lean:28) and `value_sum_le` (:51): a linear combination of tensors
    on common spaces is a restriction of their full direct sum — PROVED by the explicit matrices
    `fun x (p : ι × X) => if p.2 = x then 1 else 0` (:54–61) and scalar restriction (:31–37).
    This is the paper's "identify the corresponding variables and absorb each scalar coefficient
    into one leg".
21. `value_coefficient_le` (Degeneration.lean:67–85): coefficient d of a polynomial tensor of
    degree ≤ D is Σ_{i<D+1} w_i · P(node_i) with Lagrange weights; nodes
    `interpolationNode D i = i+1` (Interpolation.lean:23), injective and nonzero (:25–34); the
    polynomial fact is `Tensor.coeff_eq_sum_eval` (ComplexPolynomialApproximation.lean:20–33, from
    Mathlib `Lagrange.eq_interpolate`).
22. `value_le_of_polynomialApproximation` (Degeneration.lean:89–125): for the n-th tensor power
    (`PolynomialApproximation.power`, ComplexPolynomialApproximation.lean:91–115: degree ≤ D·n,
    leading coefficient index d·n equals U^{⊗n}), interpolate at D·n+1 nodes; each evaluation is
    (P(t))^{⊗n}, so χ ≤ b^n; total χ(U)^n ≤ (nD+1) b^n; `le_of_pow_le_linear_mul_pow`
    (PolynomialOverhead.lean:47) removes the linear factor (b^j·(jK+1)·(a/b)^j → 0 argument,
    :22–44). = paper's λ(B)^j ≤ (jL+1) λ(A)^j, j-th roots, j → ∞.
23. `value_polynomialRestrictionDegeneration_le` (Degeneration.lean:141–158): applies 22 with
    b = χ(T), noting each evaluation at t is `restrict (eval t ∘ maps) T`
    (`restrictionDegeneration_eval`, Interpolation.lean:105–113), hence ≤ χ(T) by `monotone`.
    D = Lx+Ly+Lz (`restrictionDegeneration_degree`, Interpolation.lean:117–135). = Lemma 2.3.
    No continuity of χ is used. Consumers: Sector/Character.lean:82, Determinant/Character.lean:141
    (grep), FiniteSeparation.lean:72 (via 22).

Six permutations ((4.3)–(4.4)):

24. `swap23Character` (Permutation.lean:144–172) = χ∘(swap legs 2,3), proved a Character.
    `permutedCharacter i := ![χ, cyc χ, cyc² χ, swap23 χ, cyc(swap23 χ), cyc²(swap23 χ)] i`
    (:179–182). Unfolding the values gives T evaluated in orders xyz, yzx, zxy, xzy, yxz, zyx —
    all six elements of S₃, each once (I unfolded the composites by hand; matches
    `prod_permutedCharacter_value`, :185–193, against `sixfoldProduct`, Symmetrization.lean:30–36).
25. `sum_permutedCharacter_pX = 2(pX+pY+pZ)` (Permutation.lean:227–230) via simp lemmas
    cyc.pX = pZ, cyc.pY = pX, cyc.pZ = pY (:195–200, `rfl`), swap23.pX = pX, swap23.pY = pZ,
    swap23.pZ = pY (:202–224). The six first-leg exponents are pX, pZ, pY, pX, pY, pZ. Correct
    (and semantically right: B_X is symmetric in y,z; swapping legs 2,3 exchanges B_Y and B_Z).
26. `symmetrizedProfile t T := sixfoldProduct T ^ (1/(6t))` (Symmetrization.lean:94–95) = (4.4);
    invariance under cyclic/swap12/swap23/reindex (:39–112); `sixfoldProduct_convolution_comm`
    (:81–91) = "interchanging the input legs permutes the factors". Multiplicativity, ≥ 1 on
    nonzero tensors, ≤ r^6 from a rank-r decomposition (SixfoldProductBounds.lean:26–106).
    `convolution a b i j k = [i+j = k]` on Fin a, Fin b, Fin (a+b−1) (Convolution/Basic.lean:24–25)
    = C(a,b) of (4.1).

Side files in my list that belong to §3 (summary only): FiniteSeparation.lean gives
`finiteSeparation_bound : (Σ_h χ(B_h))·M^{pX} ≤ 5M·χ(sharedFirstTensor B)` (:237–241) from an
explicit polynomial whose nonzero evaluations are restrictions of 5M copies (`separationPolynomial_eval`
in Separation/Basic.lean, NOT read) and `separationTarget = ⊕_h B_h ⊗ B_X(M)` (Separation/Basic.lean:332).
TagInequality.lean turns it into the entropy tag inequality via exact-type words
(`integral_type_comparison`, :111–141; `sharedFirst_tag`, :156). SharedPadding/SupportExtension
are zero-extension invariance lemmas (value unchanged), proved through `value_extendByZero`
(CharacterBounds.lean:31). The Foundation `Complex*` files are rank/border-rank bookkeeping
(batching, separated decompositions, local fiber maps, Fourier rank of a group tensor, Stirling
remainder bounds) — definitions checked below, none affects the character interface.

## 3. Definitions checked

| Lean name | file:line | what it is | matches paper? | note |
|---|---|---|---|---|
| `Tensor K X Y Z` | ComplexTensor.lean:16 | `X → Y → Z → K` | yes | finiteness via `Fintype` args |
| `rankOne` | ComplexTensor.lean:24 | a x · b y · c z | yes | outer product |
| `RankAtMost` | ComplexTensor.lean:27 | ∃ r rank-one summands, arbitrary vectors | yes | |
| `restrict` | ComplexTensor.lean:31 | Σ A x' x B y' y C z' z T x y z | yes | arbitrary matrices; Strassen order |
| `product` | ComplexTensor.lean:41 | Kronecker, legs paired | yes | |
| `directSum` | ComplexTensor.lean:45 | block-diag, label equal on all 3 legs | yes | full direct sum, common shape |
| `sumTensor` | DirectSum.lean:22 | binary full direct sum, X⊕U etc. | yes | differing shapes |
| `power` | ComplexTensor.lean:49 | ∏_i T(x_i,y_i,z_i) | yes | |
| `pullback` | ComplexTensor.lean:202 | T(fx x, fy y, fz z) | n/a | `= restrict` by 0/1 matrices (:206) |
| `BorderRankAtMost`, `DegeneratesTo` | ComplexTensor.lean:230,239 | closure of rank-r set / restriction orbit | n/a | NOT used by any Character theorem (grep) |
| `matrixMultiplication` | Complexity.lean:137 | Σ x_ij y_jk z_ki | yes | T_n for a=b=c |
| `matrixCoefficients` | ComplexMatrixTensor.lean:87 | same on arbitrary A,B,C | yes | rfl-equal |
| `dotPairing U` | ComplexDotPairing.lean:16 | z·Σ x_i y_i | yes (= B_Z) | |
| `cyclic` | ComplexTensorSymmetrization.lean:14 | (cyclic T) y z x = T x y z | yes | |
| `pairingTriple` | ComplexPairingMatrixTensor.lean:99 | B_Z(b)⊗B_Y(a)⊗B_X(c) | yes | explicit reindex to T(a,b,c) |
| `exactRank` | RankExponent.lean:36 | least r with RankAtMost | yes (R) | |
| `exactRankExponent` | RankExponent.lean:146 | inf_{n≥2} log_n R(T_n) | yes (ν) | |
| `FiniteTensor`, `TensorClass` | Semiring.lean:126,174 | Fin-presented tensors mod mutual restriction | yes (S) | Antisymmetrization, not a sigma type |
| `unitTensor` | Character/Basic.lean:24 | 1 on PUnit³ | yes (xyz = 1) | |
| `scalarTensor r` | Character/Basic.lean:27 | diagonal ⟨r⟩ | yes (integer r) | class = (r : S), Scalar.lean:147 |
| `Character` | Character/Basic.lean:35 | normalized, additive (ι-sums), multiplicative, restriction-monotone, ≥0 | yes (Def 2.1) | ≃ monotone ring homs S→ℝ, Characters.lean:166 |
| `cyclicCharacter` | Dot.lean:29 | χ∘cyclic | yes | is a Character |
| `pZ`,`pY`,`pX` | Dot.lean:107,111,114 | log₂ χ(B_Z(2)), log₂ χ(B_Y(2)), log₂ χ(B_X(2)) | yes | |
| `meanExponent` | Convolution/Symmetry.lean:76 | (pX+pY+pZ)/3 | yes (t) | positivity not proved, E2 |
| `PolynomialRestrictionDegeneration` | ComplexPolynomialDegenerationComposition.lean:94 | polynomial leg maps, leading ε^k coeff = U, lower vanish | ⊇ paper's ⇝ | E3 |
| `PolynomialApproximation` | ComplexPolynomialApproximation.lean:60 | polynomial tensor with leading coeff d = T, degree ≤ D | n/a | `rank_bound` field irrelevant to χ use |
| `interpolationNode D i` | Interpolation.lean:23 | i+1 ∈ ℂ | yes (D+1 distinct nonzero) | |
| `swap23Character` | Permutation.lean:144 | χ∘(swap legs 2,3) | yes | is a Character |
| `permutedCharacter` | Permutation.lean:179 | the 6 elements of S₃ | yes | |
| `sixfoldProduct`, `symmetrizedProfile` | Symmetrization.lean:30,94 | ∏_π λ_π(T), ^(1/(6t)) | yes (4.4) | |
| `convolution a b` | Convolution/Basic.lean:24 | Σ x_i y_j z_{i+j} | yes (4.1) | |
| `sharedFirstTensor`, `separationTarget` | Separation/Basic.lean:46,169 | shared x-leg blocks; ⊕ B_h⊗B_X(M) | (§3) | only definitions glanced |

## 4. Escalations (with resolution)

E1 (resolved). Universe: `Character.value` ranges over index types in `Type` only
(Basic.lean:36). Every tensor on my route is over `Type`: `Fin`, `Unit`, `PUnit`, products/sums/
sigmas/`Fin n →` of these (T_d over `Fin d × Fin d`, B_X/B_Y/B_Z over `Fin m`/`Unit`,
`convolution` over `Fin`). The semiring is built on `Fin`-presentations (Semiring.lean:126) and
`classOf` accepts `Type*` (Semiring.lean:187), and `ofTensorClassHom` only needs `Type`. No
universe gap. `map_directSum` is over arbitrary finite ι : Type with ARBITRARY `DecidableEq` (so
the `open scoped Classical` in CharacterBounds/SupportExtension/SharedPadding/TagInequality cannot
create an instance mismatch).

E2 (resolved, harmless). The paper's remark that T_m ≥ m forces pX+pY+pZ ≥ 1, hence t > 0, is not
formalized (grep for `one_le`/`pX + χ.pY + χ.pZ` lemmas over the subtree found none). The proof
instead splits on `0 < meanExponent` (Polynomial/Inequalities.lean:110–115); the `t ≤ 0` branch gives
t ≤ 3/4 trivially. Since only an UPPER bound on t is used downstream, the missing lower bound costs
nothing. Every lemma needing t > 0 (`convolutionProfile_le` etc., Convolution/Symmetry.lean:127–142)
takes `ht : 0 < meanExponent` explicitly, so there is no hidden division-by-zero semantics in the
`rpow (1/(6t))`.

E3 (resolved for my part; consumer-side check belongs to the §4 reader). Lemma 2.3's hypothesis in
Lean is `PolynomialRestrictionDegeneration`, polynomial (non-negative powers of ε) substitutions,
not the paper's integer-weight recipe with possibly negative weights. Every paper weight-degeneration
is one of these after multiplying each leg by a power of ε (shifts k), so the Lean notion is at least
as general and Lemma 2.3 is proved for it. The interpolation is also slightly different from the
paper's: it extracts the ε^{kn} coefficient of the n-th power (degree ≤ (Lx+Ly+Lz)n) with Lagrange
weights at nodes 1..Dn+1, rather than the constant coefficient after a shift; both give
χ(U)^n ≤ (Dn+1)·χ(T)^n. Nonzero nodes are not even needed in Lean (evaluating polynomial maps at 0
is still a restriction) — they are needed in the paper only because of negative weights. Whether
the specific degenerations of Lemmas 4.1/4.2 are correctly instantiated as this structure is for the
reader of Sector/Determinant (Sector/Character.lean:82, Determinant/Character.lean:141).

E4 (resolved). Two notions of degeneration exist: closure-based `DegeneratesTo` /
`BorderRankAtMost` (ComplexTensor.lean:230–242) and the polynomial one. Characters are NOT shown or
assumed monotone under the topological one; grep shows `DegeneratesTo`/`BorderRankAtMost` used only
in rank/border-rank files (CoppersmithWinograd/, Separation/, Convolution/Rank.lean,
AuxiliarySeparation/Separation/Basic.lean, …), and the character theorems consume only
`value_polynomialRestrictionDegeneration_le` / `value_le_of_polynomialApproximation`. No gap.

E5 (resolved). The Character structure is not vacuous: each leg-flattening rank satisfies all
seven fields (checked numerically below for additivity/multiplicativity on samples; the fields are
textbook properties of matrix rank). It is also not weaker than Def 2.1: `tensorClassHomEquiv`
(Characters.lean:166) proves the Lean structure is in bijection with monotone semiring
homomorphisms S → ℝ, which is exactly Def 2.1. Additivity on varying-shape direct sums is derived
(BinaryCharacter.lean:242), not an extra assumption.

E6 (note, not a defect). Docstring drift: Existence.lean:11,23 calls the detecting lemma
"Lemma 3.1"; the paper numbers it Lemma 2.2. Character/Basic.lean:13 refers to "Section 3 of the
paper" for the classes (paper §2). MultiplicativePower.lean:10 says "Section 3.1" (paper §2.1),
PolynomialOverhead.lean:10 "Section 4" (paper §2.2). Statements are unaffected.

E7 (checked). `attribute [...]` lines: `grep -rn "attribute \["` over all 31 assigned files returns
none. No `local instance` in my part can alter a statement's meaning. `open scoped Classical` appears
in CharacterBounds.lean:17, SupportExtension.lean:127, SharedPadding.lean:18, TagInequality.lean:22 —
harmless per E1.

E8 (minor, checked). `Character` takes `value` with explicit `Fintype` instances as arguments; since
`Fintype` is a subsingleton the value cannot depend on the instance in a meaningful way, and
`value_reindex` (Basic.lean:73) only uses `monotone`.

## 5. Independent computation

Script `<scratch>/readB/flat.py`
(`python3 -I`, exact rank over ℚ by Fraction Gaussian elimination; tensors built to mirror the Lean
definitions: `matrixMultiplication` guard, `dotPairing`, `cyclic`).

- Flattening ranks (X,Y,Z) of T_n, n=1..5: [1,1,1], [4,4,4], [9,9,9], [16,16,16], [25,25,25] = n².
- B_X(m)=cyclic²(dotPairing): (1, m, m); B_Y(m)=cyclic(dotPairing): (m, 1, m); B_Z(m)=dotPairing:
  (m, m, 1), m=1..5. So the X-flattening character has (pX,pY,pZ) = (0,1,1), Y-flattening (1,0,1),
  Z-flattening (1,1,0); each sums to 2 and gives n² on T_n, consistent with (2.4).
- B_X(m)⊗B_Y(m)⊗B_Z(m) has the same flattening ranks as T_m (m=1..3).
- `value_matrixCoefficients` formula χ(T(a,b,c)) = b^{pZ} a^{pY} c^{pX} checked for all three
  flattening characters at (a,b,c) ∈ {(1,2,3),(2,3,4),(3,1,2)}: X-flat = ab, Y-flat = bc,
  Z-flat = ca, all matched.
- Multiplicativity T(2,2,2)⊗T(1,2,3): [8,24,12] = product of factors; additivity T(2,2,2)⊕T(1,2,3):
  [6,10,7] = sum.
- (4.3) for the X-flattening: six first-leg exponents (0,1,1,0,1,1) sum to 4 = 2·2. Trivially consistent.

## 6. Verdict

The tensor foundations and the character interface mean what the paper says: `Character` is
provably equivalent to Definition 2.1 (monotone semiring homomorphisms from tensors modulo mutual
restriction), pX/pY/pZ are log₂ of the character on the three oriented 2-dimensional dot products,
(2.3)–(2.4) and p ∈ [0,1] are proved by the paper's own sandwich argument and an explicit reindexing,
Lemma 2.3 is proved (for a notion of degeneration at least as general as the paper's) by tensor-power
interpolation without continuity, and the six permuted characters are all of S₃ with
Σ p_X^{(π)} = 2(pX+pY+pZ); I found no discrepancy, only that t > 0 is replaced by a harmless case split.

Not read: the proof of `exists_detecting_character` and the Spectrum/ modules (reader C);
Separation/Basic.lean beyond the definitions cited (in particular `separationPolynomial_eval`,
`separationPolynomial_coeff_zero`, `separationPolynomial_degree`); Entropy/Tag.lean
(`tag_of_integral_type_comparison`); Convolution/ and Polynomial/Inequalities.lean beyond the lines
cited; the Sector/ and Determinant/ degenerations that instantiate Lemma 2.3; the rest of
ComplexPolynomialDegenerationComposition.lean (lines other than the structure and `cyclic`);
RankExponent.lean proofs; Complexity.lean (arithmetic model, `AdmissibleExponent`).
