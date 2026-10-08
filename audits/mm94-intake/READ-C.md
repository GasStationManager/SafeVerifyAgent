# READ-C: detecting characters (paper Lemma 2.2, Appendix A)

Reader C. Part: does a character with λ(T_d) ≥ k exist for every k < d^ν? This covers states on
the tensor semiring S, Lemma A.1 (multiplicativity from a fixed-point theorem), the state space K,
why K is nonempty (Farkas → rationals → Grothendieck group → catalyst), and the obstruction argument.
All paths below are relative to
`/home/user/openai-math/repo/lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/`
unless stated otherwise. Paper = `scratchpad/mm94paper/paper.txt`, lines 98–105 and 456–560.

## 1. Files read

Read whole, leaves first (line counts from `wc -l`):

| file | lines |
|---|---|
| Tensor/DirectSum.lean | 139 |
| Tensor/Semiring.lean | 541 |
| Tensor/DirectSumClass.lean | 75 |
| Tensor/Scalar.lean | 140 |
| Tensor/Characters.lean | 178 |
| Convex/ConeSupport.lean | 103 |
| Convex/FiniteConeClosed.lean | 75 |
| Convex/RationalSpan.lean | 48 |
| Convex/RationalDenominators.lean | 44 |
| Convex/RationalCone.lean | 203 |
| Convex/Farkas.lean | 72 |
| Convex/FixedPoint.lean | 226 |
| Spectrum/Coordinates.lean | 68 |
| Spectrum/NormalizedStates.lean | 145 |
| Spectrum/MultiplicativeStates.lean | 232 |
| Spectrum/Catalyst.lean | 85 |
| Spectrum/StateObstruction.lean | 308 |
| Spectrum/Obstruction.lean | 369 |
| Character/Existence.lean | 49 |
| Arithmetic/RankExponent.lean | 225 |
| Growth/SpectralLimit.lean | 76 (extra: Obstruction.lean consumes it) |

Partly read:
- Growth/PolynomialOverhead.lean, lines 1–90 of 97 (`le_of_eventually_pow_le_const_mul_pow`).
- Character/Basic.lean, lines 24–75 (`unitTensor`, `scalarTensor`, `structure Character`).
- `../Tensor/ComplexTensor.lean`, lines 15–50 (`Tensor`, `restrict`, `product`, `directSum`).
- `../Tensor/ComplexMatrixTensor.lean`, lines 10–40 (`matrixCoefficients`).
- External package `.lake/packages/fixed-point-theorems`: I read the statement of
  `brouwer_fixed_point` (brouwer.lean:14–25), its local diff, and grepped the package for
  sorry/axiom/admit/native_decide/unsafe/implemented_by/elab/macro. The only hits were calls to
  `axiomOfChoice`, and that is a core *theorem* (Init/Classical.lean:122).

## 2. Argument reconstruction

Every lemma in the Spectrum and Convex files is abstract. Each is stated over a general
`[CommSemiring S] [Preorder S]` and takes its order facts as explicit hypotheses. Existence.lean
then discharges those hypotheses with theorems about the real `TensorClass`.

1. **S and its order.** `TensorClass := Antisymmetrization FiniteTensor (· ≤ ·)`
   (Tensor/Semiring.lean:174). A `FiniteTensor` has dimensions in ℕ and complex coefficients
   (126–130). `T ≤ S` means `IsRestriction`: there are linear maps A, B, C with
   T = restrict A B C S (32–34, 143). `Tensor.restrict` is the genuine trilinear restriction,
   Σ A·B·C·T (ComplexTensor.lean:31–35). Addition is `sumTensor`, a block direct sum
   (DirectSum.lean:22–26). Multiplication is the Kronecker product. The semiring laws are proved by
   reindexing (Semiring.lean:281–380).
2. **Order facts, proved as theorems.** `mul_mono` (382), `add_mono` (390), `zero_le` (399),
   `rank` descending to classes (425), `rank_mono` (437), `rank_mul_le` (442),
   `matrixClass_mul` (465), `matrixClass_pow` (488), `Nontrivial` (503), and
   `one_le_of_ne_zero` (530). The last holds because a nonzero coefficient restricts to the unit
   tensor (512–527). Scalar.lean adds `classOf (scalarTensor r) = r` (72) and
   `classOf T ≤ r ↔ RankAtMost T r` (96), so ℕ ⊂ S is "r disjoint scalar products". It also adds
   `le_rank : T ≤ rank T` (108) and `natCast_le_natCast_iff` (117).
3. **State space K.** `normalizedStates R d k ⊆ (S → ℝ)` (NormalizedStates.lean:23–27) is cut out
   by five conditions:
   - 0 ≤ f x ≤ R x
   - f 1 = 1
   - f(x+y) = f x + f y
   - x ≤ y → f x ≤ f y
   - k·f x ≤ f(d·x)

   This is exactly the paper's K, with (A.1) as the last condition and d = T_d.
   - Closed: 29–53.
   - Compact: Mathlib's Tychonoff, `isCompact_univ_pi` on ∏[0, R x] (55–60).
   - Convex: 62–91.
   - f 0 = 0 follows from additivity (93–97).
   - `state_rescale` (116–139) is the paper's "P_z preserves K". Its proof needs 1 ≤ z, z·x ≤ z·y
     whenever x ≤ y, and z·x ≤ R(x)·z (the paper's "zx ≤ R(x)z").
4. **Nonemptiness of K (paper A.2, first half).** `normalizedStates_nonempty_of_no_catalyst`
   (StateObstruction.lean:277–302).
   - **Compactness and the finite subsystem.** B = ∏[0, R x] is compact by `isCompact_pi_infinite`
     (288). Each constraint set is closed (291). It is then enough that every finite family of
     constraints is solvable inside B ∩ {f 1 = 1}, via `inter_iInter_nonempty` (300). This is the
     paper's "finite inconsistent subsystem", run in the contrapositive.
   - **Constraints as integer vectors.** The constraints are an inductive type `StateConstraint`
     (28–34). Each becomes an integer vector in `S →₀ ℤ` (37–46). Additivity contributes both
     signs; there is no quotient by the relation vectors.
   - **Bounded solution.** `bounded_finite_stateConstraint_solution` (227–273) adds lower and upper
     bound constraints for every coordinate in the finite support H. Outside H the solution is
     extended by 0 (`finiteCoordinateState`, Coordinates.lean:19).
   - **Farkas on the finite support.** `finite_stateConstraint_solution` (179–223) applies
     `exists_normalized_nonneg_linear_of_no_nat_certificate` (Farkas.lean:162). Its alternative is
     "∃ m > 0 and n : I → ℕ with Σ nᵢ vᵢ = −m·e₁".
   - **From a certificate to a catalyst.** `no_stateConstraint_certificate` (156–175) pushes such a
     certificate into Mathlib's `Algebra.GrothendieckAddGroup S` with
     `Finsupp.linearCombination ℤ of`. Each vector maps to
     `[upper] − [lower] + [d·s] − k[s]` (138–152). Then
     `exists_catalyst_of_completion_sum_eq` (Catalyst.lean:56) produces
     `D + m + d·s ≤ D + k·s`, which is paper (A.2). It uses `AddLocalization.exists_of_eq`, so
     equality in the Grothendieck group gives equality after adding a common element C
     (Catalyst.lean:43). The catalyst is D = C + Y (44).
5. **Farkas machinery (Convex/).**
   - `exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed` (Farkas.lean:122–157):
     if −u is not in the real cone C, Mathlib's `ProperCone.hyperplane_separation_point` gives f.
     Normalizing it gives L(u) = 1 and L ≥ 0 on the generators.
   - Membership −u ∈ C would produce a real nonnegative solution. That is turned into a natural
     certificate by `exists_nat_scaled_int_solution_of_nonneg_real` (RationalCone.lean:279).
   - Closedness of a finitely generated cone is proved locally: Carathéodory-style reduction to
     linearly independent subfamilies (ConeSupport.lean:67–99), then each such cone is the image
     of the orthant under a closed embedding (FiniteConeClosed.lean:29–71).
   - **Rationality** (RationalSpan.lean:22–44, RationalCone.lean:118–243). A ℚ-linear map
     p : ℝ → ℚ that fixes ℚ comes from `Module.Projective.exists_dual_eq_one`. Applied to a real
     solution it yields a rational solution. Nonnegativity is kept by a second step:
     `eq_pos_convex_span_of_mem_convexHull` writes the point with affinely independent support,
     where the weights are unique, so p fixes them. Denominators are then cleared
     (RationalDenominators.lean:77–88).
   - **Why integrality matters.** The paper must read the certificate in the Grothendieck group
     with ℕ multiplicities: `n • [x]` is meaningful there, a real multiple is not. Lean needs this
     for the same reason, since `Catalyst.lean` takes `n : I → ℕ`.
6. **Obstruction (paper "Ruling out the obstruction").** `no_tensor_catalytic_gain`
   (Obstruction.lean:357–363) says: if k < d^ν, then no D, s and m > 0 satisfy
   D + m + T_d·s ≤ D + k·s. The proof chain:
   - **s ≠ 0** (`tensor_catalytic_obstruction_of_positive_scalar_gain`, 342–353). If s = 0 the
     comparison reads D + m ≤ D. Iterating gives n·m ≤ D, hence n·m ≤ rank D for every n
     (311–337).
     *Different from the paper:* the paper rules this out with flattening rank. Lean uses
     monotonicity of tensor rank, which is equally valid.
   - **Iteration, (A.3)** (`catalytic_power_comparison`, 172–211). From D + t·s ≤ D + k·s:
     - Additive iteration gives D + m·t·s ≤ D + m·k·s.
     - Absorbing D ≤ R(D)·s gives n·t·s ≤ (nk + R(D))·s.
     - Multiplicative induction gives nʲ tʲ s ≤ Kʲ s with K = nk + R(D).

     There is no cancellation anywhere; this matches the paper.
   - **Rank bound at fixed j** (`catalytic_semiring_obstruction`, 217–247). From
     `hbudget : R(T_g) ≤ nʲ → T_g ≤ nʲ` (Obstruction.lean:265–279, via `le_rank` and natCast
     monotonicity), T_{dʲg} = T_dʲ·T_g ≤ T_dʲ·nʲ·s ≤ Kʲ·s. Taking rank gives
     R(T_{dʲg}) ≤ R(s)·Kʲ.
   - **The slack u, for finite j** (`catalytic_rank_bound_at_slack`, 88–142). Pick u with
     R(T_u) < u^{ν+δ} (`exists_exactMatrixRank_lt_rpow`, RankExponent.lean:204). Put
     ℓ = ⌊j·log_u n/τ⌋ and g = u^ℓ (104–105). Two explicit bounds follow:
     - R(T_g) ≤ R(T_u)^ℓ ≤ nʲ (`exactMatrixRank_pow_le`, 26–39; `floor_rank_power_bounds`, 43–83).
     - n^{j/τ} ≤ u·g.

     Combined with R(T_N) ≥ N^ν (`exactMatrixRank_rpow_lower_of_pos`, RankExponent.lean:196) this
     gives (d^ν n^{ν/τ})ʲ ≤ (u^ν R(s))·Kʲ for every j ≥ 1. This is an explicit inequality at each
     finite j. Only then does `le_of_eventually_pow_le_const_mul_pow` (PolynomialOverhead.lean:52)
     drop the constant: if bʲ ≤ C aʲ eventually, then b ≤ a, proved with a limit of (a/b)ʲ.
   - **The choice of u disappears.** The conclusion is d^ν n^{ν/(ν+δ)} ≤ nk + R(D). It mentions
     neither u nor R(s). This is the paper's "the choice of u has disappeared", and it is honest:
     u is existentially chosen inside the proof for each δ.
   - **δ → 0, then n → ∞** (`spectral_coefficient_le_of_all_nat`, SpectralLimit.lean:65–72):
     - First δ = 1/(m+1) → 0 at fixed n, using continuity of rpow (20–44). This gives
       d^ν·n ≤ nk + R(D).
     - Then n → ∞ (48–61), giving d^ν ≤ k.

     The order of the limits matches the paper, and it matters (see §4, E5).
7. **Multiplicativity (Lemma A.1).** `exists_multiplicative_of_invariant_states`
   (MultiplicativeStates.lean:155–184) together with `exists_finite_multiplicative_slice`
   (111–150).
   - **One map at a time.** Induct over a finite set t of nonzero z. In the current slice C (compact,
     convex, invariant under every P_w), the map `normalizedTranslate z` (f ↦ f(z·)/f(z), 17–18) is
     continuous, because f z ≥ 1 > 0 on K (20–26, 131). Schauder–Tychonoff gives a fixed point g
     (132).
   - **Freeze the eigenvalue.** Set c = g(z) and pass to the slice C ∩ {f(z·x) = c·f(x) ∀x}
     (`frozenSlice`, 31). This slice is convex because c is a constant (49–58), compact (45),
     nonempty because it contains g (141), and invariant under every P_w (60–72). This is the
     paper's K′, word for word.
   - **All maps at once.** The finite intersection property in the compact space K gives a common
     solution of f(zx) = f(z)f(x) for all z ≠ 0 (180). The case z = 0 uses f 0 = 0 (182–183).
   - **Linearization.** The P_z themselves are not affine, and the fixed-point theorem is applied to
     the nonlinear but continuous P_z. Linear (convex) structure is needed only for the slices, and
     it is obtained by freezing c, exactly as in the paper.
8. **Schauder–Tychonoff (Convex/FixedPoint.lean).** `compact_convex_fixedPoint` (202–216) is
   proved here, by the Schauder projection.
   - Fix a finite coordinate set s and ε > 0. Cover the compact K by finitely many sets
     {x : |a_j,i − x_i| < ε for i ∈ s}. Take a subordinate partition of unity w_j (Mathlib
     `PartitionOfUnity.exists_isSubordinate`, 102–142).
   - Map the standard simplex into K by v ↦ Σ v_j a_j. Apply Brouwer to
     v ↦ (w_j(f(Σ v a)))_j on the simplex in `Fin n → ℝ` (74–75).
   - The result is an approximate fixed point on the coordinates in s (79–100).
   - The finite intersection property over (coordinate, ε) pairs then gives an exact fixed point
     (159–197).
   - Brouwer itself, `brouwer_fixed_point`, comes from the external package
     `fixed-point-theorems` (harfe, commit 770940dd, proved via cubical Sperner), with a local
     Lean 4.34.1 compatibility patch. Mathlib does not have it at this pin.
9. **Assembly.** `exists_detecting_character` (Character/Existence.lean:25–43):
   - Instantiate with S = TensorClass, R = rank, d = matrixClass d, and k.
   - Nonemptiness comes from step 4 with `hno` supplied by step 6 (Existence.lean:28–32).
   - `hdom` is z·x ≤ z·R(x) = R(x)·z (33–38).
   - Step 7 then gives a monotone ring hom φ : TensorClass →+* ℝ with k ≤ φ(matrixClass d) (39–42).
   - `Character.ofTensorClassHom φ hφ` (Characters.lean:111–132) turns φ into a `Character`. The
     detector value is φ(classOf T_d), which is definitionally φ(matrixClass d)
     (Semiring.lean:451).

   This statement is Lemma 2.2: d ≥ 2, k : ℕ, (k:ℝ) < d^ν ⇒ ∃ χ, k ≤ χ(T_d). Its only consumer is
   Arithmetic/RankBound.lean:21. Note the docstring calls it "Lemma 3.1", which looks like
   paper-version drift.

## 3. Definitions checked

| Lean name | file:line | what it is | matches paper? | note |
|---|---|---|---|---|
| `IsRestriction` | Tensor/Semiring.lean:32 | T = restrict A B C S for arbitrary linear A, B, C | yes (A ≤ B) | `restrict` = Σ A B C T, ComplexTensor.lean:31 |
| `TensorClass` | Semiring.lean:174 | finite ℂ-tensors modulo mutual restriction | yes (S) | order via Mathlib `Antisymmetrization`; `tensorClass_le_iff` is `Iff.rfl` (183) |
| `+`, `*`, `0`, `1` | Semiring.lean:223–275 | block direct sum, Kronecker product, empty tensor, 1×1×1 tensor of 1 | yes | `nsmul := nsmulRec`; natCast is the default unary cast, checked = scalarTensor (Scalar.lean:72) |
| `rank` | Semiring.lean:425 | exact tensor rank (`Nat.find` of a decomposition, RankExponent.lean:36) | yes (R) | |
| `matrixClass n` | Semiring.lean:451 | class of `matrixMultiplication n n n` = coefficients x=(i,j), y=(j,k), z=(k,i) | yes (T_n, cyclic convention) | ComplexMatrixTensor.lean:17–22 |
| `scalarTensor r` | Character/Basic.lean:27 | diagonal unit tensor ⟨r⟩ | yes | |
| `exactRankExponent` | RankExponent.lean:146 | sInf{log_n R(T_n) : n ≥ 2} | yes ((2.2)) | set nonempty and bounded below by 2 (148, 169) |
| `Character` | Character/Basic.lean:35–55 | nonneg, f(0) = 0, f(1) = 1, additive on finite direct sums, multiplicative, restriction-monotone, on Type-0 coordinates | yes (Def 2.1) | |
| `normalizedStates` | Spectrum/NormalizedStates.lean:23 | bounds [0, R], f 1 = 1, additive, monotone, k f x ≤ f(d x) | yes (K) | λ(0) = 0 derived (93) |
| `normalizedTranslate` | MultiplicativeStates.lean:17 | f ↦ f(z·)/f z | yes (P_z) | |
| `frozenSlice` | MultiplicativeStates.lean:31 | C ∩ {f(z x) = c f x} | yes (K′) | |
| `StateConstraint` / `stateConstraintVector` | StateObstruction.lean:28–46 | homogeneous integer constraint vectors | yes | equalities as two inequalities instead of a quotient (equivalent) |
| `GrothendieckAddGroup` | Mathlib, used Catalyst.lean:25 | additive completion of (S, +) | yes | real Mathlib object, not a stand-in |
| `ofTensorClassHom` | Tensor/Characters.lean:111 | φ ↦ (T ↦ φ(classOf T)) | yes | directSum over any Fintype ι via `classOf_directSum` (DirectSumClass.lean:47); monotone via `classOf_le_iff`; `map_one` is definitional, since `One` is classOf of the PUnit unit tensor = `unitTensor` |
| `compact_convex_fixedPoint` | Convex/FixedPoint.lean:202 | Schauder–Tychonoff in I → ℝ for compact convex K | yes (the theorem the paper cites) | proved here from external Brouwer |

## 4. Escalations

- **E1 (dependency, informational): Brouwer comes from a third-party package outside the scanned
  subtree.** FixedPoint.lean:1 imports `FixedPointTheorems.brouwer` from
  `harfe/fixed-point-theorems-lean4` (lakefile.lean:10–11, pinned commit 770940dd). It is patched
  locally by `patches/fixed-point-theorems-lean4341.patch` (640 lines; the local diff touches 5
  .lean files, +78/−111).
  - The brief's mechanical scan covers the *solution subtree*. This package is not in it, and
    neither is the patch.
  - My grep of the package found no sorry, axiom, admit, native_decide, unsafe, implemented_by,
    elab or macro. The only "axiom" text is `axiomOfChoice`, a core theorem.
  - The diff to brouwer.lean changes imports, comments and `simpa` → `simpa using!`. The statement
    is unchanged.
  - The coordinator's `#print axioms` on the headline will certify it either way. Recommend that
    the coordinator's scan list include this package and the patch.
- **E2 (resolved): is the fixed-point step a real theorem?** Yes. The Schauder projection
  (partition of unity + Brouwer on a finite simplex + finite intersection property) is fully proved
  in FixedPoint.lean:45–216. It is not assumed, and not replaced by a weaker statement.
  Hypotheses: compact, convex and nonempty K ⊆ I → ℝ with the product topology, and continuous
  f : K → K. These are exactly the paper's.
- **E3 (resolved): could the abstract lemmas be satisfied only trivially?** No.
  - Every hypothesis of the abstract lemmas (`hzero`, `hbound`, `hadd`, `hunit`, `hmulmono`, `hdom`,
    `hno`) is discharged in Existence.lean:28–42 by *theorems* about `TensorClass`. These are
    `zero_le`, `le_rank`, `add_mono`, `mul_mono` and `one_le_of_ne_zero`, proved at
    Semiring.lean:382–535 and Scalar.lean:108.
  - None of them is a typeclass axiom instantiated trivially.
  - `TensorClass` is `Nontrivial` (Semiring.lean:503).
  - `k < d^ν` is satisfiable, for example k = 0.
  - The ambient index type `TensorClass` is arbitrary (uncountable). Nothing enumerates it. Every
    finiteness step is over a `Finset` of constraints or of nonzero elements.
- **E4 (resolved): local instances.** My files contain no `attribute [...]` lines (grep). The
  `instance` declarations in Semiring.lean (143–503) define the order as restriction and the
  operations as ⊕ and ⊗, all verified above.
- **E5 (informational): the order of limits is load-bearing.** At fixed δ, the post-j inequality
  nk + R(D) ≥ d^ν n^{ν/(ν+δ)} is *not* contradictory for all n. It fails on a window of n and
  then holds again for astronomically large n. With d=2, k=4, R(D)=10, ν=2.3, δ=0.01 it fails
  from n = 1e2 through 1e20 and holds again from n = 1e21 on.

  The contradiction needs δ → 0 at fixed n *before* n → ∞. The paper does this, and so does Lean
  (`spectral_coefficient_le_of_all_nat` = `coefficient_le_of_nat_mul_bound` ∘
  `spectral_bound_of_positive_slack`, SpectralLimit.lean:65–72).
- **E6 (cosmetic).** The Existence.lean docstring (11, 23) says "Lemma 3.1"; the paper calls it
  Lemma 2.2. The proof of s ≠ 0 uses tensor-rank monotonicity (Obstruction.lean:311–337), not the
  paper's flattening rank. Both are valid; Lean's argument needs no rank additivity.

**Independent numeric check** (`scratchpad/a3check.py`, 20 lines, run with `python3 -I`). Inputs:
d=2, k=4, m=1, R(D)=10, ν=2.3, δ=0.01, u=2. Then d^ν = 4.9246 > 4.
- The post-j bound nk + R(D) ≥ d^ν n^{ν/τ} holds at n = 1 and n = 10, and fails at
  n = 1e2 … 1e6. At n = 1e6 the sides are 4.0e6 vs 4.64e6.
- After δ → 0, the bound fails for every n > R(D)/(d^ν − k) ≈ 10.8.
- At finite j with n = 1e4 and R(s) = 5, the explicit inequality
  ν·log(dʲ g_j) ≤ log R(s) + j log K holds at j = 1 and j = 10 and is violated from j = 100 on.
- So the paper's contradiction is numerically real.

## 5. Verdict and what I did not read

**Verdict:** this part is a faithful and complete formalization of Lemma 2.2 / Appendix A,
including a genuine proof of Schauder–Tychonoff on top of Brouwer, an actual Grothendieck group,
honest finite-j inequalities, and limits taken in the right order. The only thing outside the
scanned subtree is the external Brouwer package (E1).

Not read:
- `fixed-point-theorems` bodies: cubical Sperner, convex homeomorphisms (about 2,900 lines). Only
  the statement and a grep.
- Tensor/BinaryCharacter.lean, which Characters.lean imports but no step I traced consumes.
- `../Tensor/ComplexTensorFlattening.lean` (`card_le_of_identity`, used for rank lower bounds).
- `../Tensor/ComplexTensorRestrictionComposition.lean` (`restrict_restrict`, `pullback_eq_restrict`,
  `RankAtMost.restrict/product/power/pullback`).
- The rest of Character/Basic.lean beyond lines 24–75.
- PolynomialOverhead.lean lines 90–97.
- Mathlib lemmas, trusted by name and signature: `ProperCone.hyperplane_separation_point`,
  `isCompact_pi_infinite`, `PartitionOfUnity.exists_isSubordinate`,
  `AddLocalization.exists_of_eq`, `eq_pos_convex_span_of_mem_convexHull`.
