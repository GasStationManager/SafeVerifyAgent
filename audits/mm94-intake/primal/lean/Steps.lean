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
  sorry

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
  sorry

theorem classOf_branchWordTensor_exact (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (w : ExactWords counts) :
    classOf (branchWordTensor B w.val) = ∏ a, classOf (B a) ^ counts a := by
  sorry

/-- Leg permutations commute with word tensors (definitionally), so the symmetrised class of a
word tensor is the product of the symmetrised classes of its letters. -/
theorem sym6class_branchWordTensor (B : Fin s → Tensor ℂ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    sym6class (branchWordTensor B w) = ∏ i, sym6class (B (w i)) := by
  sorry

theorem sym6class_branchWordTensor_exact (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (w : ExactWords counts) :
    sym6class (branchWordTensor B w.val) = ∏ a, sym6class (B a) ^ counts a := by
  sorry

/-! ### The separated target as a class -/

/-- `separationTarget B` is the direct sum of the branches, each tensored with the dot product
`B_X(M)`; as a class, the sum of the branch classes times `dotX M`. -/
theorem classOf_separationTarget {M : ℕ} (B : Fin M → Tensor ℂ X Y Z) :
    classOf (separationTarget B) = (∑ h, classOf (B h)) * dotX M := by
  sorry

/-- The exact-type restriction of the `N`-th power of a shared-first tensor is a shared-first
tensor of word tensors; its class is below the `N`-th power. -/
theorem classOf_sharedFirst_words_le (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    classOf (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      classOf (sharedFirstTensor B) ^ (∑ a, counts a) := by
  sorry

/-- One Fourier-separation round, symmetrised: `5M` copies of the `N`-th power of a
shared-first family degenerate to `M` copies of the branch product of type `counts`, times
`T_M²`.  Here `M = Fintype.card (ExactWords counts)` and `N = ∑ counts`. -/
theorem degClass_sym6_round (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ) :
    DegClass (((5 * Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 *
        sym6class (sharedFirstTensor B) ^ (∑ a, counts a))
      (((Fintype.card (ExactWords counts) : ℕ) : TensorClass) ^ 6 *
        (∏ a, sym6class (B a) ^ counts a) *
        matrixClass (Fintype.card (ExactWords counts)) ^ 2) := by
  sorry

end SharedFirst

/-! ### Lemma 4.1: the determinant filtration -/

section Filtration

open DeterminantFiltration

/-- The dot product on the second and third legs with a trivial first leg. -/
abbrev dotYZ (U : Type) [DecidableEq U] : Tensor ℂ Unit U U :=
  Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) U))

theorem sym6class_dotYZ_bool : sym6class (dotYZ Bool) = matrixClass 2 ^ 2 := by
  sorry

/-- Lemma 4.1 as a single-leg degeneration: `C(d+1, e+1) ⊗ B(2)` degenerates to the two
branches `C(d+1, e+2)`, `C(d+1, e)` sharing their first leg. -/
theorem deg_filtration (d e : ℕ) :
    Deg (Tensor.product (convolution (d + 1) (e + 1)) (dotYZ Bool))
      (sharedFirstTensor (branch d e)) := by
  sorry

theorem convolution_le_branch_zero (d e : ℕ) :
    classOf (convolution (d + 1) (e + 2)) ≤ classOf (branch d e 0) := by
  sorry

theorem convolution_le_branch_one (d e : ℕ) :
    classOf (convolution (d + 1) e) ≤ classOf (branch d e 1) := by
  sorry

/-- The E-step: Lemma 4.1 followed by one separation round at type `(cp, cm)`, symmetrised.
`a = d + 1`, `b = e + 1`. -/
theorem Estep (d e cp cm : ℕ) :
    DegClass (((5 * Fintype.card (ExactWords ![cp, cm]) : ℕ) : TensorClass) ^ 6 *
        (S (d + 1) (e + 1) * matrixClass 2 ^ 2) ^ (cp + cm))
      (((Fintype.card (ExactWords ![cp, cm]) : ℕ) : TensorClass) ^ 6 *
        S (d + 1) (e + 2) ^ cp * S (d + 1) e ^ cm *
        matrixClass (Fintype.card (ExactWords ![cp, cm])) ^ 2) := by
  sorry

end Filtration

/-! ### Lemma 4.2: the three sectors -/

section Sectors

open Sector

/-- Lemma 4.2 as a single-leg degeneration: `C(a, 3h+a-1)` degenerates to the three sector
branches sharing their first leg. -/
theorem deg_sector (a h : ℕ) :
    Deg (convolution a (sourceWidth a h)) (sharedFirstTensor (branchFamily a h)) := by
  sorry

/-- Each sector branch is at least `C(a,h)` up to a leg permutation. -/
theorem S_le_sym6class_branchFamily (a h : ℕ) (b : Fin 3) :
    S a h ≤ sym6class (branchFamily a h b) := by
  sorry

/-- The F-step: Lemma 4.2 followed by one separation round at type `(c₀, c₁, c₂)`,
symmetrised. -/
theorem Fstep (a h c₀ c₁ c₂ : ℕ) :
    DegClass (((5 * Fintype.card (ExactWords ![c₀, c₁, c₂]) : ℕ) : TensorClass) ^ 6 *
        S a (sourceWidth a h) ^ (c₀ + c₁ + c₂))
      (((Fintype.card (ExactWords ![c₀, c₁, c₂]) : ℕ) : TensorClass) ^ 6 *
        S a h ^ (c₀ + c₁ + c₂) *
        matrixClass (Fintype.card (ExactWords ![c₀, c₁, c₂])) ^ 2) := by
  sorry

end Sectors

end Primal

end

end OAI
