import Audit.Primal.Classes
import Audit.Primal.Separation
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Character
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Character
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.BranchTagging
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting

set_option linter.unusedSectionVars false

/-!
# The two LP steps as class-level degenerations (audit, not part of the artifact)

The growth lemma of the paper is linear in `(log λ, t)`; its LP dual is a primal construction
built from the paper's own degenerations.  This file states the two constraint families as
degenerations between symmetrised classes:

* `Estep` (Lemma 4.1 + Proposition 3.1 + Corollary 3.2):
  `(5M)^6 · (S(a,b) · T₂²)^N ⇝ M^6 · S(a,b+1)^{c₊} · S(a,b−1)^{c₋} · T_M²`,
  `N = c₊ + c₋`, `M = #words of type (c₊, c₋) = C(N, c₊)`;
* `Fstep` (Lemma 4.2 + Proposition 3.1 + Corollary 3.2):
  `(5M)^6 · S(a,3h+a−1)^N ⇝ M^6 · S(a,h)^N · T_M²`,
  `N = c₀ + c₁ + c₂`, `M = #words of type (c₀, c₁, c₂)`.

Both are the same mechanism: a single-leg degeneration into a shared-first family of branches
(`deg_filtration`, `deg_sector`), tensor powers restricted to the words of one exact type
(`exactType_power_pullback`), the degree-tracked separation of `Separation.lean`, and the
class computation of the separated target.  Symmetrisation over the six leg permutations is
done once, through `sym6class`.
-/

namespace OAI

open MatrixMultiplication.Foundation
open MatrixMultiplication.AuxiliarySeparation
open MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section

namespace Primal

section SharedFirst

variable {s : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- With recoverable labels, the shared-first tensor is a zero-extension of the plain sum of
the branches (the converse of the artifact's `sharedFirstTensor_pullback_labels`). -/
theorem sharedFirstTensor_eq_restrict_sum [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (B : Fin s → Tensor ℂ X Y Z) (ly : Y → Fin s) (lz : Z → Fin s)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    sharedFirstTensor B = Tensor.restrict
      (fun (x : X) (x' : X) => if x' = x then (1 : ℂ) else 0)
      (fun (y : Fin s × Y) (y' : Y) => if y' = y.2 ∧ ly y.2 = y.1 then (1 : ℂ) else 0)
      (fun (z : Fin s × Z) (z' : Z) => if z' = z.2 ∧ lz z.2 = z.1 then (1 : ℂ) else 0)
      (∑ i, B i) := by
  funext x y z
  obtain ⟨i, y⟩ := y
  obtain ⟨j, z⟩ := z
  have hsum : (∑ k, B k x y z) = B (ly y) x y z := by
    apply Finset.sum_eq_single (ly y)
    · intro k _ hk
      by_contra h
      exact hk (hsupport k x y z h).1.symm
    · simp
  simp only [Tensor.restrict, Finset.sum_apply]
  rw [Fintype.sum_eq_single x (fun x' hx' => by simp [hx']),
    Fintype.sum_eq_single y (fun y' hy' => by simp [hy']),
    Fintype.sum_eq_single z (fun z' hz' => by simp [hz'])]
  simp only [true_and, ite_true, one_mul, hsum]
  change (if i = j then B i x y z else 0) = _
  by_cases hb : B (ly y) x y z = 0
  · rw [hb, mul_zero]
    split_ifs with hij
    · by_contra h
      rw [← (hsupport i x y z h).1] at h
      exact h hb
    · rfl
  · obtain ⟨-, hz⟩ := hsupport (ly y) x y z hb
    rw [hz]
    by_cases hy : ly y = i
    · subst hy
      by_cases hj : ly y = j
      · subst hj
        simp
      · simp [hj]
    · rw [ite_eq_right hy, zero_mul, zero_mul]
      split_ifs with hij
      · by_contra h
        exact hy (hsupport i x y z h).1
      · rfl

theorem deg_sum_sharedFirst [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (B : Fin s → Tensor ℂ X Y Z) (ly : Y → Fin s) (lz : Z → Fin s)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    Deg (∑ i, B i) (sharedFirstTensor B) := by
  rw [sharedFirstTensor_eq_restrict_sum B ly lz hsupport]
  exact Deg.of_restrict _ _ _ _

/-! ### Words of an exact type -/

/-- The class of a word tensor is the product of the classes of its letters. -/
theorem classOf_branchWordTensor (B : Fin s → Tensor ℂ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    classOf (branchWordTensor B w) = ∏ i, classOf (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (fun (_ _ _ : PUnit.{1}) => (1 : ℂ)) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback]
      rw [hzero, classOf_reindex, Finset.univ_eq_empty, Finset.prod_empty]
      rfl
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, classOf_reindex, classOf_product, ih, Fin.prod_univ_succ]
      rfl

theorem classOf_branchWordTensor_exact (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (w : ExactWords counts) :
    classOf (branchWordTensor B w.val) = ∏ a, classOf (B a) ^ counts a := by
  rw [classOf_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => classOf (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

/-- Leg permutations commute with word tensors (definitionally), so the symmetrised class of a
word tensor is the product of the symmetrised classes of its letters. -/
theorem sym6class_branchWordTensor (B : Fin s → Tensor ℂ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    sym6class (branchWordTensor B w) = ∏ i, sym6class (B (w i)) := by
  have h1 : classOf (Tensor.cyclic (branchWordTensor B w)) =
      ∏ i, classOf (Tensor.cyclic (B (w i))) :=
    classOf_branchWordTensor (fun a => Tensor.cyclic (B a)) w
  have h2 : classOf (Tensor.cyclic (Tensor.cyclic (branchWordTensor B w))) =
      ∏ i, classOf (Tensor.cyclic (Tensor.cyclic (B (w i)))) :=
    classOf_branchWordTensor (fun a => Tensor.cyclic (Tensor.cyclic (B a))) w
  have h3 : classOf (swapYZ (branchWordTensor B w)) =
      ∏ i, classOf (swapYZ (B (w i))) :=
    classOf_branchWordTensor (fun a => swapYZ (B a)) w
  have h4 : classOf (Tensor.cyclic (swapYZ (branchWordTensor B w))) =
      ∏ i, classOf (Tensor.cyclic (swapYZ (B (w i)))) :=
    classOf_branchWordTensor (fun a => Tensor.cyclic (swapYZ (B a))) w
  have h5 : classOf (Tensor.cyclic (Tensor.cyclic (swapYZ (branchWordTensor B w)))) =
      ∏ i, classOf (Tensor.cyclic (Tensor.cyclic (swapYZ (B (w i))))) :=
    classOf_branchWordTensor (fun a => Tensor.cyclic (Tensor.cyclic (swapYZ (B a)))) w
  unfold sym6class
  rw [classOf_branchWordTensor, h1, h2, h3, h4, h5]
  simp only [← Finset.prod_mul_distrib]

theorem sym6class_branchWordTensor_exact (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (w : ExactWords counts) :
    sym6class (branchWordTensor B w.val) = ∏ a, sym6class (B a) ^ counts a := by
  rw [sym6class_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => sym6class (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

/-! ### The separated target as a class -/

/-- `separationTarget B` is the direct sum of the branches, each tensored with the dot product
`B_X(M)`; as a class, the sum of the branch classes times `dotX M`. -/
theorem classOf_separationTarget {M : ℕ} (B : Fin M → Tensor ℂ X Y Z) :
    classOf (separationTarget B) = (∑ h, classOf (B h)) * dotX M := by
  rw [separationTarget_eq_directSum, classOf_reindex, classOf_directSum]
  simp only [classOf_product, Finset.sum_mul]
  rfl

/-- The exact-type restriction of the `N`-th power of a shared-first tensor is a shared-first
tensor of word tensors; its class is below the `N`-th power. -/
theorem classOf_sharedFirst_words_le (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    classOf (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      classOf (sharedFirstTensor B) ^ (∑ a, counts a) := by
  rw [← exactType_power_pullback B counts e, ← classOf_power]
  exact (classOf_le_iff _ _).mpr (IsRestriction.pullback _ _ _ _)

/-- One Fourier-separation round, symmetrised: `5M` copies of the `N`-th power of a
shared-first family degenerate to `M` copies of the branch product of type `counts`, times
`T_M²`.  Here `M = Fintype.card (ExactWords counts)` and `N = ∑ counts`. -/
theorem degClass_sym6_round (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ) :
    DegClass (((5 * Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 *
        sym6class (sharedFirstTensor B) ^ (∑ a, counts a))
      (((Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 *
        (∏ a, sym6class (B a) ^ counts a) *
        matrixClass (Fintype.card (ExactWords counts)) ^ 2) := by
  have hM : 0 < Fintype.card (ExactWords counts) :=
    Fintype.card_pos_iff.mpr (exactWords_nonempty counts)
  let e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts :=
    (Fintype.equivFin (ExactWords counts)).symm
  let B' : Fin (Fintype.card (ExactWords counts)) →
      Tensor ℂ (Fin (∑ a, counts a) → X) (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  -- the degree-tracked separation, symmetrised
  have hdeg := DegClass.sym6 (deg_separation hM B')
  rw [sym6class_copies] at hdeg
  -- the source: the exact-type words sit below the `N`-th power
  have hle : sym6class (sharedFirstTensor B') ≤
      sym6class (sharedFirstTensor B) ^ (∑ a, counts a) := by
    rw [← sym6class_power]
    apply sym6class_mono
    rw [classOf_power]
    exact classOf_sharedFirst_words_le B counts e
  -- the target: `M` copies of one word tensor times the dot product
  let w₀ : ExactWords counts := e ⟨0, hM⟩
  let D := Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ)
    (Fin (Fintype.card (ExactWords counts)))))
  let W := Tensor.directSum (fun _ : Fin (Fintype.card (ExactWords counts)) =>
    Tensor.product (branchWordTensor B w₀.val) D)
  have hclass : classOf (separationTarget B') = classOf W := by
    rw [classOf_separationTarget, classOf_copies, classOf_product,
      classOf_branchWordTensor_exact]
    simp only [B', classOf_branchWordTensor_exact, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_assoc]
    rfl
  have htgt : sym6class (separationTarget B') =
      ((Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 *
        (∏ a, sym6class (B a) ^ counts a) *
        matrixClass (Fintype.card (ExactWords counts)) ^ 2 := by
    rw [sym6class_congr hclass, sym6class_copies, sym6class_product,
      sym6class_branchWordTensor_exact, sym6class_dot, mul_assoc]
  rw [htgt] at hdeg
  exact hdeg.mono_left (mul_mono le_rfl hle)

end SharedFirst

/-! ### Lemma 4.1: the determinant filtration -/

section Filtration

open DeterminantFiltration

/-- The dot product on the second and third legs with a trivial first leg. -/
abbrev dotYZ (U : Type) [DecidableEq U] : Tensor ℂ Unit U U :=
  Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) U))

theorem sym6class_dotYZ_bool : sym6class (dotYZ Bool) = matrixClass 2 ^ 2 := by
  have ht : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv (dotYZ Bool) =
      dotYZ (Fin 2) := by
    funext i j k
    simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing]
  rw [← sym6class_reindex (dotYZ Bool) (Equiv.refl Unit) finTwoEquiv finTwoEquiv, ht]
  exact sym6class_dot 2

/-- Lemma 4.1 as a single-leg degeneration: `C(d+1, e+1) ⊗ B(2)` degenerates to the two
branches `C(d+1, e+2)`, `C(d+1, e)` sharing their first leg. -/
theorem deg_filtration (d e : ℕ) :
    Deg (Tensor.product (convolution (d + 1) (e + 1)) (dotYZ Bool))
      (sharedFirstTensor (branch d e)) := by
  have h₁ : Deg (Tensor.product (convolution (d + 1) (e + 1)) (dotYZ Bool))
      (sourceTensor d e) := by
    rw [sourceTensor_product]
    exact Deg.of_pullback _ _ _ _
  have h₂ : Deg (sourceTensor d e) (adaptedTensor d e) := by
    rw [← sourceTensor_coordinate_change d e]
    exact Deg.of_restrict _ _ _ _
  have h₃ : Deg (adaptedTensor d e) (gradedTensor d e) :=
    ⟨_, _, _, _, ⟨degeneration d e⟩⟩
  have h₄ : Deg (gradedTensor d e) (sharedFirstTensor (branch d e)) := by
    rw [← sum_branch d e]
    exact deg_sum_sharedFirst (branch d e) (branchLabel e) (branchLabel (d + e))
      (branch_support d e)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem convolution_le_branch_zero (d e : ℕ) :
    classOf (convolution (d + 1) (e + 2)) ≤ classOf (branch d e 0) := by
  let fz : Fin ((d + 1) + (e + 2) - 1) → Index (d + e) :=
    fun k => .inl (Fin.cast (by omega) k)
  have ht : Tensor.pullback id Sum.inl fz (branch d e 0) =
      convolution (d + 1) (e + 2) := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  rw [classOf_le_iff, ← ht]
  exact IsRestriction.pullback _ _ _ _

theorem convolution_le_branch_one (d e : ℕ) :
    classOf (convolution (d + 1) e) ≤ classOf (branch d e 1) := by
  let fz : Fin ((d + 1) + e - 1) → Index (d + e) :=
    fun k => .inr (Fin.cast (by omega) k)
  have ht : Tensor.pullback id Sum.inr fz (branch d e 1) =
      convolution (d + 1) e := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  rw [classOf_le_iff, ← ht]
  exact IsRestriction.pullback _ _ _ _

/-- `degClass_sym6_round` with its exponent and its branch product in a prescribed form (the
exponent also occurs inside the `Fintype (ExactWords counts)` instance, so it cannot be
rewritten in place). -/
private theorem degClass_sym6_round_of_eq {s : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y]
    [Fintype Z] (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ) {N : ℕ} {P : TensorClass}
    (hN : ∑ a, counts a = N) (hP : ∏ a, sym6class (B a) ^ counts a = P) :
    DegClass (((5 * Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 *
        sym6class (sharedFirstTensor B) ^ N)
      (((Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 * P *
        matrixClass (Fintype.card (ExactWords counts)) ^ 2) := by
  subst hN hP
  exact degClass_sym6_round B counts

/-- The E-step: Lemma 4.1 followed by one separation round at type `(cp, cm)`, symmetrised.
`a = d + 1`, `b = e + 1`. -/
theorem Estep (d e cp cm : ℕ) :
    DegClass (((5 * Fintype.card (ExactWords ![cp, cm]) : ℕ) : TensorClass) ^ 6 *
        (S (d + 1) (e + 1) * matrixClass 2 ^ 2) ^ (cp + cm))
      (((Fintype.card (ExactWords ![cp, cm]) : ℕ) : TensorClass) ^ 6 *
        S (d + 1) (e + 2) ^ cp * S (d + 1) e ^ cm *
        matrixClass (Fintype.card (ExactWords ![cp, cm])) ^ 2) := by
  have hsum : (∑ a, (![cp, cm] : Fin 2 → ℕ) a) = cp + cm := by
    simp [Fin.sum_univ_two]
  have hprod : (∏ a, sym6class (branch d e a) ^ (![cp, cm] : Fin 2 → ℕ) a) =
      sym6class (branch d e 0) ^ cp * sym6class (branch d e 1) ^ cm := by
    simp [Fin.prod_univ_two]
  have hS : S (d + 1) (e + 1) * matrixClass 2 ^ 2 =
      sym6class (Tensor.product (convolution (d + 1) (e + 1)) (dotYZ Bool)) := by
    rw [sym6class_product, sym6class_dotYZ_bool, S]
  have h₁ := (DegClass.refl
      (((5 * Fintype.card (ExactWords ![cp, cm]) : ℕ) : TensorClass) ^ 6)).mul
    ((DegClass.sym6 (deg_filtration d e)).pow (cp + cm))
  have h₂ := degClass_sym6_round_of_eq (branch d e) ![cp, cm] hsum hprod
  rw [hS]
  refine (h₁.trans h₂).mono_right ?_
  have h0 : S (d + 1) (e + 2) ≤ sym6class (branch d e 0) :=
    sym6class_mono (convolution_le_branch_zero d e)
  have h1 : S (d + 1) e ≤ sym6class (branch d e 1) :=
    sym6class_mono (convolution_le_branch_one d e)
  rw [mul_assoc (((Fintype.card (ExactWords ![cp, cm]) : ℕ) : TensorClass) ^ 6)
    (S (d + 1) (e + 2) ^ cp)]
  exact mul_mono (mul_mono le_rfl (mul_mono (pow_le_pow_left' h0 cp)
    (pow_le_pow_left' h1 cm))) le_rfl

end Filtration

/-! ### Lemma 4.2: the three sectors -/

section Sectors

open Sector

/-- Lemma 4.2 as a single-leg degeneration: `C(a, 3h+a-1)` degenerates to the three sector
branches sharing their first leg. -/
theorem deg_sector (a h : ℕ) :
    Deg (convolution a (sourceWidth a h)) (sharedFirstTensor (branchFamily a h)) := by
  have h₁ : Deg (convolution a (sourceWidth a h)) (retained a h) :=
    ⟨_, _, _, _, ⟨restriction a h⟩⟩
  have h₂ : Deg (retained a h) (sharedFirstTensor (branchFamily a h)) := by
    rw [← sum_branchFamily a h]
    exact deg_sum_sharedFirst (branchFamily a h) (yLabel a h) (zLabel a h)
      (branchFamily_labels a h)
  exact h₁.trans h₂

/-- Each sector branch is at least `C(a,h)` up to a leg permutation. -/
theorem S_le_sym6class_branchFamily (a h : ℕ) (b : Fin 3) :
    S a h ≤ sym6class (branchFamily a h b) := by
  fin_cases b
  · show S a h ≤ sym6class (branchFamily a h 0)
    rw [branchFamily_zero]
    apply sym6class_mono
    rw [classOf_le_iff, ← leftTensor_pullback a h]
    exact IsRestriction.pullback _ _ _ _
  · show S a h ≤ sym6class (branchFamily a h 1)
    rw [branchFamily_one, S, ← sym6class_swapYZ (convolution a h)]
    apply sym6class_mono
    have hx : swapYZ (convolution a h) = exchangedConvolution a h := rfl
    rw [classOf_le_iff, hx, ← middleTensor_pullback a h]
    exact IsRestriction.pullback _ _ _ _
  · show S a h ≤ sym6class (branchFamily a h 2)
    rw [branchFamily_two]
    apply sym6class_mono
    rw [classOf_le_iff, ← rightTensor_pullback a h]
    exact IsRestriction.pullback _ _ _ _

/-- The F-step: Lemma 4.2 followed by one separation round at type `(c₀, c₁, c₂)`,
symmetrised. -/
theorem Fstep (a h c₀ c₁ c₂ : ℕ) :
    DegClass (((5 * Fintype.card (ExactWords ![c₀, c₁, c₂]) : ℕ) : TensorClass) ^ 6 *
        S a (sourceWidth a h) ^ (c₀ + c₁ + c₂))
      (((Fintype.card (ExactWords ![c₀, c₁, c₂]) : ℕ) : TensorClass) ^ 6 *
        S a h ^ (c₀ + c₁ + c₂) *
        matrixClass (Fintype.card (ExactWords ![c₀, c₁, c₂])) ^ 2) := by
  have hsum : (∑ b, (![c₀, c₁, c₂] : Fin 3 → ℕ) b) = c₀ + c₁ + c₂ := by
    simp [Fin.sum_univ_three]
  have hprod : (∏ b, sym6class (branchFamily a h b) ^ (![c₀, c₁, c₂] : Fin 3 → ℕ) b) =
      sym6class (branchFamily a h 0) ^ c₀ * sym6class (branchFamily a h 1) ^ c₁ *
        sym6class (branchFamily a h 2) ^ c₂ := by
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h₁ := (DegClass.refl
      (((5 * Fintype.card (ExactWords ![c₀, c₁, c₂]) : ℕ) : TensorClass) ^ 6)).mul
    ((DegClass.sym6 (deg_sector a h)).pow (c₀ + c₁ + c₂))
  have h₂ := degClass_sym6_round_of_eq (branchFamily a h) ![c₀, c₁, c₂] hsum hprod
  refine (h₁.trans h₂).mono_right ?_
  have hb := S_le_sym6class_branchFamily a h
  have hle : S a h ^ (c₀ + c₁ + c₂) ≤
      sym6class (branchFamily a h 0) ^ c₀ * sym6class (branchFamily a h 1) ^ c₁ *
        sym6class (branchFamily a h 2) ^ c₂ := by
    rw [pow_add, pow_add]
    exact mul_mono (mul_mono (pow_le_pow_left' (hb 0) c₀) (pow_le_pow_left' (hb 1) c₁))
      (pow_le_pow_left' (hb 2) c₂)
  exact mul_mono (mul_mono le_rfl hle) le_rfl

end Sectors

end Primal

end

end OAI
