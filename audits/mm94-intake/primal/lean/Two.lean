import Audit.Primal.Steps
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy

set_option linter.unusedSectionVars false

/-!
# The `a₀ = 2` primal construction (audit, not part of the artifact)

The exact LP certificate at `a₀ = 2` is `20·E(2,2; 7/10) + 14·E(2,3; 9/14) + 9·F(2,1)` (÷15).
Per unit `N = 210 m` of the tensor power this reads

  `⟨5^258⟩ ⊗ Cat ⊗ S(2,2)^{15N} ⊗ T_{2^{68N}}  ⇝  Cat ⊗ T_{B_N}`,

  `Cat = ⟨M₁^120 M₂^84 M₃^54⟩ ⊗ S(2,3)^{14N} ⊗ S(2,4)^{9N} ⊗ S(2,2)^{5N}`,
  `B_N = 2^{30N} M₁^40 M₂^28 M₃^18`,
  `M₁ = C(N, 7N/10)`, `M₂ = C(N, 9N/14)`, `M₃ = N!/((N/3)!)³`.

`two_cat_degeneration` is that statement, an identity in the commutative semiring of tensor
classes once the three steps are multiplied.  The rest of the file is the standard passage
from a catalytic degeneration to the exact-rank exponent: iterate the catalyst, interpolate
(Bini), remove the catalyst and the linear overhead (`PolynomialOverhead`), and bootstrap the
matrix factor on the left (Schönhage).  The limit is `ν ≤ 90 log 3 / (β − 68 log 2) ≈ 2.7375`
with `β = 30 log 2 + 40 H(7/10) + 28 H(9/14) + 18 log 3`.
-/

namespace OAI

open MatrixMultiplication.Foundation
open MatrixMultiplication.AuxiliarySeparation
open MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section

namespace Primal

/-! ### Catalytic degenerations and the exponent -/

/-- Iterating a catalytic degeneration. -/
theorem DegClass.catalytic_pow {A L R : TensorClass} (h : DegClass (A * L) (A * R)) (n : ℕ) :
    DegClass (A * L ^ n) (A * R ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, mul_one]
    exact DegClass.refl A
  | succ n ih =>
    have e₁ : A * L ^ (n + 1) = A * L * L ^ n := by ring
    have e₂ : A * R * L ^ n = A * L ^ n * R := by ring
    have e₃ : A * R ^ n * R = A * R ^ (n + 1) := by ring
    have h₁ : DegClass (A * L * L ^ n) (A * R * L ^ n) := DegClass.mul h (DegClass.refl _)
    have h₂ : DegClass (A * L ^ n * R) (A * R ^ n * R) := DegClass.mul ih (DegClass.refl _)
    rw [e₁, ← e₃]
    rw [e₂] at h₁
    exact h₁.trans h₂

theorem rank_pow_le (c : TensorClass) (n : ℕ) : rank (c ^ n) ≤ rank c ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, ← Nat.cast_one, rank_natCast]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (rank_mul_le _ _).trans (Nat.mul_le_mul ih le_rfl)

theorem natCast_ne_zero_class {n : ℕ} (hn : 0 < n) : (n : TensorClass) ≠ 0 := by
  intro h
  have h' := congrArg rank h
  rw [rank_natCast, ← Nat.cast_zero, rank_natCast] at h'
  omega

theorem mul_ne_zero_class {c d : TensorClass} (hc : c ≠ 0) (hd : d ≠ 0) : c * d ≠ 0 := by
  have h1 : (1 : TensorClass) ≤ c * d := by
    simpa using mul_mono (one_le_of_ne_zero hc) (one_le_of_ne_zero hd)
  intro h0
  rw [h0] at h1
  exact one_ne_zero (le_antisymm h1 (TensorSemiring.zero_le 1))

/-- From a catalytic degeneration `A ⊗ L ⇝ A ⊗ T_b`, Bini interpolation and removal of the
catalyst give `ν ≤ log_b (rank L)`. -/
theorem exactRankExponent_le_of_catalytic {A L : TensorClass} {b : ℕ} (hA : A ≠ 0) (hb : 2 ≤ b)
    (h : DegClass (A * L) (A * matrixClass b)) :
    exactRankExponent ≤ Real.logb b (rank L) := by
  set ν := exactRankExponent
  have hA1 : (1 : TensorClass) ≤ A := one_le_of_ne_zero hA
  have hApow : ∀ j : ℕ, (1 : TensorClass) ≤ A ^ j := fun j => one_le_pow₀ hA1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  -- Step 1: for every `n`, `(b^ν)^n ≤ rank A * (rank L)^n`.
  have key : ∀ n : ℕ, ((b : ℝ) ^ ν) ^ n ≤ (rank A : ℝ) * (rank L : ℝ) ^ n := by
    intro n
    obtain ⟨D, hD⟩ := ApproxClass.rank_pow
      (ApproxClass.of_degClass (DegClass.catalytic_pow h n) (ApproxClass.of_rank (A * L ^ n)))
    have hρ : rank (A * L ^ n) ≤ rank A * rank L ^ n :=
      (rank_mul_le _ _).trans (Nat.mul_le_mul_left _ (rank_pow_le _ _))
    have hlow : ∀ j : ℕ,
        exactMatrixRank (b ^ (n * j)) ≤ (D * j + 1) * rank (A * L ^ n) ^ j := by
      intro j
      have h1 : matrixClass b ^ (n * j) ≤ (A * matrixClass b ^ n) ^ j := by
        rw [mul_pow, ← pow_mul]
        calc matrixClass b ^ (n * j) = 1 * matrixClass b ^ (n * j) := (one_mul _).symm
          _ ≤ A ^ j * matrixClass b ^ (n * j) := mul_mono (hApow j) le_rfl
      have h2 := rank_mono h1
      rw [← matrixClass_pow, rank_matrixClass] at h2
      exact h2.trans (hD j)
    have hreal : ∀ j : ℕ, (((b : ℝ) ^ n) ^ ν) ^ j ≤
        ((j : ℝ) * D + 1) * ((rank A : ℝ) * (rank L : ℝ) ^ n) ^ j := by
      intro j
      have hpos : 0 < b ^ (n * j) := pow_pos (by omega) _
      have hl1 := exactMatrixRank_rpow_lower_of_pos hpos
      have heq : (((b : ℝ) ^ n) ^ ν) ^ j = (((b ^ (n * j) : ℕ) : ℝ)) ^ ν := by
        rw [Nat.cast_pow, pow_mul, Real.rpow_pow_comm (by positivity)]
      calc (((b : ℝ) ^ n) ^ ν) ^ j = (((b ^ (n * j) : ℕ) : ℝ)) ^ ν := heq
        _ ≤ (exactMatrixRank (b ^ (n * j)) : ℝ) := hl1
        _ ≤ (((D * j + 1) * rank (A * L ^ n) ^ j : ℕ) : ℝ) := by exact_mod_cast hlow j
        _ ≤ ((j : ℝ) * D + 1) * ((rank A : ℝ) * (rank L : ℝ) ^ n) ^ j := by
          push_cast
          rw [mul_comm (D : ℝ) (j : ℝ)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast hρ
    rw [Real.rpow_pow_comm hb0.le]
    exact le_of_pow_le_linear_mul_pow (by positivity) hreal
  -- Step 2: remove the catalyst.
  have hbL : (b : ℝ) ^ ν ≤ (rank L : ℝ) :=
    le_of_pow_le_const_mul_pow (Nat.cast_nonneg _) key
  -- Step 3: take logarithms.
  have hLpos : (0 : ℝ) < (rank L : ℝ) := (Real.rpow_pos_of_pos hb0 ν).trans_le hbL
  exact (Real.le_logb_iff_rpow_le hb1 hLpos).mpr hbL

/-! ### The construction at `a₀ = 2` -/

namespace Two

/-- `M₁ = C(210m, 147m)`, the number of words of type `(7/10, 3/10)`. -/
def M₁ (m : ℕ) : ℕ := Fintype.card (ExactWords ![147 * m, 63 * m])

/-- `M₂ = C(210m, 135m)`, the number of words of type `(9/14, 5/14)`. -/
def M₂ (m : ℕ) : ℕ := Fintype.card (ExactWords ![135 * m, 75 * m])

/-- `M₃ = (210m)! / ((70m)!)³`, the number of words of the uniform three-letter type. -/
def M₃ (m : ℕ) : ℕ := Fintype.card (ExactWords ![70 * m, 70 * m, 70 * m])

/-- The catalyst. -/
def Cat (m : ℕ) : TensorClass :=
  ((M₁ m : ℕ) : TensorClass) ^ 120 * ((M₂ m : ℕ) : TensorClass) ^ 84 *
    ((M₃ m : ℕ) : TensorClass) ^ 54 *
    S 2 3 ^ (14 * (210 * m)) * S 2 4 ^ (9 * (210 * m)) * S 2 2 ^ (5 * (210 * m))

/-- The matrix size produced per unit. -/
def B (m : ℕ) : ℕ := 2 ^ (30 * (210 * m)) * M₁ m ^ 40 * M₂ m ^ 28 * M₃ m ^ 18

/-- The source per unit. -/
def L (m : ℕ) : TensorClass :=
  (5 : TensorClass) ^ 258 * S 2 2 ^ (15 * (210 * m)) * matrixClass 2 ^ (68 * (210 * m))

/-- The `a₀ = 2` certificate as a catalytic degeneration. -/
theorem two_cat_degeneration (m : ℕ) : DegClass (Cat m * L m) (Cat m * matrixClass (B m)) := by
  have h₁ : DegClass ((((5 * M₁ m : ℕ) : TensorClass) ^ 6 *
        (S 2 2 * matrixClass 2 ^ 2) ^ (147 * m + 63 * m)) ^ 20)
      ((((M₁ m : ℕ) : TensorClass) ^ 6 * S 2 3 ^ (147 * m) * S 2 1 ^ (63 * m) *
        matrixClass (M₁ m) ^ 2) ^ 20) :=
    (Estep 1 1 (147 * m) (63 * m)).pow 20
  have h₂ : DegClass ((((5 * M₂ m : ℕ) : TensorClass) ^ 6 *
        (S 2 3 * matrixClass 2 ^ 2) ^ (135 * m + 75 * m)) ^ 14)
      ((((M₂ m : ℕ) : TensorClass) ^ 6 * S 2 4 ^ (135 * m) * S 2 2 ^ (75 * m) *
        matrixClass (M₂ m) ^ 2) ^ 14) :=
    (Estep 1 2 (135 * m) (75 * m)).pow 14
  have h₃ : DegClass ((((5 * M₃ m : ℕ) : TensorClass) ^ 6 *
        S 2 4 ^ (70 * m + 70 * m + 70 * m)) ^ 9)
      ((((M₃ m : ℕ) : TensorClass) ^ 6 * S 2 1 ^ (70 * m + 70 * m + 70 * m) *
        matrixClass (M₃ m) ^ 2) ^ 9) :=
    (Fstep 2 1 (70 * m) (70 * m) (70 * m)).pow 9
  have h := (h₁.mul h₂).mul h₃
  have hS : S 2 1 = matrixClass 2 ^ 2 := (S_comm 2 1).trans (S_one 2)
  have hB : matrixClass (B m) = matrixClass 2 ^ (30 * (210 * m)) * matrixClass (M₁ m) ^ 40 *
      matrixClass (M₂ m) ^ 28 * matrixClass (M₃ m) ^ 18 := by
    unfold B
    rw [matrixClass_mul, matrixClass_mul, matrixClass_mul, matrixClass_pow, matrixClass_pow,
      matrixClass_pow, matrixClass_pow]
  rw [hS, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at h
  convert h using 1
  · unfold Cat L
    set_option exponentiation.threshold 300 in ring
  · rw [hB]
    unfold Cat
    ring

private theorem M₁_pos (m : ℕ) : 0 < M₁ m := by
  have := exactWords_nonempty ![147 * m, 63 * m]
  exact Fintype.card_pos

private theorem M₂_pos (m : ℕ) : 0 < M₂ m := by
  have := exactWords_nonempty ![135 * m, 75 * m]
  exact Fintype.card_pos

private theorem M₃_pos (m : ℕ) : 0 < M₃ m := by
  have := exactWords_nonempty ![70 * m, 70 * m, 70 * m]
  exact Fintype.card_pos

private theorem pow_ne_zero_class {c : TensorClass} (hc : c ≠ 0) (n : ℕ) : c ^ n ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_ne_zero
  | succ n ih => rw [pow_succ]; exact mul_ne_zero_class ih hc

theorem Cat_ne_zero (m : ℕ) : Cat m ≠ 0 := by
  unfold Cat
  refine mul_ne_zero_class (mul_ne_zero_class (mul_ne_zero_class (mul_ne_zero_class
    (mul_ne_zero_class ?_ ?_) ?_) ?_) ?_) ?_
  · exact pow_ne_zero_class (natCast_ne_zero_class (M₁_pos m)) _
  · exact pow_ne_zero_class (natCast_ne_zero_class (M₂_pos m)) _
  · exact pow_ne_zero_class (natCast_ne_zero_class (M₃_pos m)) _
  · exact pow_ne_zero_class (S_ne_zero 2 3 (by norm_num) (by norm_num)) _
  · exact pow_ne_zero_class (S_ne_zero 2 4 (by norm_num) (by norm_num)) _
  · exact pow_ne_zero_class (S_ne_zero 2 2 (by norm_num) (by norm_num)) _

theorem two_le_B {m : ℕ} (hm : 1 ≤ m) : 2 ≤ B m := by
  unfold B
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (30 * (210 * m)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (30 * (210 * m)) * M₁ m ^ 40 := Nat.le_mul_of_pos_right _ (pow_pos (M₁_pos m) 40)
    _ ≤ 2 ^ (30 * (210 * m)) * M₁ m ^ 40 * M₂ m ^ 28 :=
      Nat.le_mul_of_pos_right _ (pow_pos (M₂_pos m) 28)
    _ ≤ 2 ^ (30 * (210 * m)) * M₁ m ^ 40 * M₂ m ^ 28 * M₃ m ^ 18 :=
      Nat.le_mul_of_pos_right _ (pow_pos (M₃_pos m) 18)

/-- The exponent bound at each unit size, before the bootstrap. -/
theorem exponent_le_logb {m : ℕ} (hm : 1 ≤ m) :
    exactRankExponent ≤ Real.logb (B m) (rank (L m)) :=
  exactRankExponent_le_of_catalytic (Cat_ne_zero m) (two_le_B hm) (two_cat_degeneration m)

/-! ### Sizes -/

theorem rank_L_le (m : ℕ) :
    rank (L m) ≤ 5 ^ 258 * 729 ^ (15 * (210 * m)) * exactMatrixRank (2 ^ (68 * (210 * m))) := by
  unfold L
  have h5 : rank ((5 : TensorClass) ^ 258) = 5 ^ 258 := by
    have e : (5 : TensorClass) ^ 258 = ((5 ^ 258 : ℕ) : TensorClass) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [e, rank_natCast]
  have hS : rank (S 2 2 ^ (15 * (210 * m))) ≤ 729 ^ (15 * (210 * m)) :=
    (rank_pow_le _ _).trans (Nat.pow_le_pow_left ((rank_S_le 2 2).trans (by norm_num)) _)
  have hT : rank (matrixClass 2 ^ (68 * (210 * m))) = exactMatrixRank (2 ^ (68 * (210 * m))) := by
    rw [← matrixClass_pow, rank_matrixClass]
  calc rank ((5 : TensorClass) ^ 258 * S 2 2 ^ (15 * (210 * m)) * matrixClass 2 ^ (68 * (210 * m)))
      ≤ rank ((5 : TensorClass) ^ 258 * S 2 2 ^ (15 * (210 * m))) *
          rank (matrixClass 2 ^ (68 * (210 * m))) := rank_mul_le _ _
    _ ≤ rank ((5 : TensorClass) ^ 258) * rank (S 2 2 ^ (15 * (210 * m))) *
          rank (matrixClass 2 ^ (68 * (210 * m))) := Nat.mul_le_mul (rank_mul_le _ _) le_rfl
    _ ≤ 5 ^ 258 * 729 ^ (15 * (210 * m)) * exactMatrixRank (2 ^ (68 * (210 * m))) := by
      rw [h5, hT]
      exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl hS) le_rfl

/-- Binary entropy. -/
def Hb (p : ℝ) : ℝ := -(p * Real.log p) - (1 - p) * Real.log (1 - p)

theorem log_M₁_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * Hb (7 / 10) - 3 * (1 + Real.log (210 * m + 1)) ≤ Real.log (M₁ m) := by
  have h := abs_log_multinomial_sub_entropy_le ![147 * m, 63 * m]
  have hM : M₁ m = Nat.multinomial Finset.univ ![147 * m, 63 * m] := by
    unfold M₁
    convert exactWords_card ![147 * m, 63 * m]
  have hs : (∑ a, ![147 * m, 63 * m] a) = 210 * m := by
    simp [Fin.sum_univ_two]; ring
  have hc : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hH : (finiteEntropy fun a => ((![147 * m, 63 * m] a : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ)) =
      Hb (7 / 10) := by
    unfold finiteEntropy
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : ((147 * m : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ) = 7 / 10 := by
      push_cast; field_simp; ring
    have e2 : ((63 * m : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ) = 3 / 10 := by
      push_cast; field_simp; ring
    rw [e1, e2]
    unfold Hb entropyTerm
    rw [show (1 : ℝ) - 7 / 10 = 3 / 10 by norm_num]
    ring
  rw [hs, hc, hH] at h
  rw [hM]
  push_cast at h
  have h' := (abs_le.mp h).1
  linarith

theorem log_M₂_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * Hb (9 / 14) - 3 * (1 + Real.log (210 * m + 1)) ≤ Real.log (M₂ m) := by
  have h := abs_log_multinomial_sub_entropy_le ![135 * m, 75 * m]
  have hM : M₂ m = Nat.multinomial Finset.univ ![135 * m, 75 * m] := by
    unfold M₂
    convert exactWords_card ![135 * m, 75 * m]
  have hs : (∑ a, ![135 * m, 75 * m] a) = 210 * m := by
    simp [Fin.sum_univ_two]; ring
  have hc : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hH : (finiteEntropy fun a => ((![135 * m, 75 * m] a : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ)) =
      Hb (9 / 14) := by
    unfold finiteEntropy
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : ((135 * m : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ) = 9 / 14 := by
      push_cast; field_simp; ring
    have e2 : ((75 * m : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ) = 5 / 14 := by
      push_cast; field_simp; ring
    rw [e1, e2]
    unfold Hb entropyTerm
    rw [show (1 : ℝ) - 9 / 14 = 5 / 14 by norm_num]
    ring
  rw [hs, hc, hH] at h
  rw [hM]
  push_cast at h
  have h' := (abs_le.mp h).1
  linarith

theorem log_M₃_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * Real.log 3 - 4 * (1 + Real.log (210 * m + 1)) ≤ Real.log (M₃ m) := by
  have h := abs_log_multinomial_sub_entropy_le ![70 * m, 70 * m, 70 * m]
  have hM : M₃ m = Nat.multinomial Finset.univ ![70 * m, 70 * m, 70 * m] := by
    unfold M₃
    convert exactWords_card ![70 * m, 70 * m, 70 * m]
  have hs : (∑ a, ![70 * m, 70 * m, 70 * m] a) = 210 * m := by
    simp [Fin.sum_univ_three]; ring
  have hc : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hH : (finiteEntropy fun a => ((![70 * m, 70 * m, 70 * m] a : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ)) =
      Real.log 3 := by
    have hv : ∀ a, (![70 * m, 70 * m, 70 * m] a) = 70 * m := by
      intro a; fin_cases a <;> rfl
    simp only [hv]
    unfold finiteEntropy
    rw [Fin.sum_univ_three]
    have e1 : ((70 * m : ℕ) : ℝ) / ((210 * m : ℕ) : ℝ) = 3⁻¹ := by
      push_cast; field_simp; ring
    rw [e1]
    unfold entropyTerm
    rw [Real.log_inv]
    ring
  rw [hs, hc, hH] at h
  rw [hM]
  push_cast at h
  have h' := (abs_le.mp h).1
  linarith

/-- The growth rate of `log B_N / N`. -/
def β : ℝ := 30 * Real.log 2 + 40 * Hb (7 / 10) + 28 * Hb (9 / 14) + 18 * Real.log 3

theorem log_B_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * β - 276 * (1 + Real.log (210 * m + 1)) ≤ Real.log (B m) := by
  have h1 := log_M₁_ge hm
  have h2 := log_M₂_ge hm
  have h3 := log_M₃_ge hm
  have p1 : (0 : ℝ) < M₁ m := by
    have : 0 < M₁ m := by unfold M₁; exact Fintype.card_pos_iff.2 (exactWords_nonempty _)
    exact_mod_cast this
  have p2 : (0 : ℝ) < M₂ m := by
    have : 0 < M₂ m := by unfold M₂; exact Fintype.card_pos_iff.2 (exactWords_nonempty _)
    exact_mod_cast this
  have p3 : (0 : ℝ) < M₃ m := by
    have : 0 < M₃ m := by unfold M₃; exact Fintype.card_pos_iff.2 (exactWords_nonempty _)
    exact_mod_cast this
  unfold B
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  unfold β
  linarith

private theorem Hb_ge_quadratic {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 2 * p * (1 - p) ≤ Hb p := by
  have hq0 : 0 < 1 - p := sub_pos.mpr hp1
  have h1 := Real.log_le_sub_one_of_pos hp0
  have h2 := Real.log_le_sub_one_of_pos hq0
  unfold Hb
  nlinarith [mul_le_mul_of_nonneg_left h1 hp0.le, mul_le_mul_of_nonneg_left h2 hq0.le]

theorem beta_sub_pos : 0 < β - 68 * Real.log 2 := by
  have h1 := Hb_ge_quadratic (p := 7 / 10) (by norm_num) (by norm_num)
  have h2 := Hb_ge_quadratic (p := 9 / 14) (by norm_num) (by norm_num)
  have h3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    linarith
  unfold β
  linarith

/-! ### The bootstrap -/

/-- Monotonicity of the exact matrix rank in the dimension. -/
theorem exactMatrixRank_mono {n n' : ℕ} (h : n ≤ n') : exactMatrixRank n ≤ exactMatrixRank n' := by
  let f : Fin n × Fin n → Fin n' × Fin n' := fun p => (Fin.castLE h p.1, Fin.castLE h p.2)
  have hpb := (exactRank_spec (Tensor.matrixMultiplication n' n' n')).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.matrixMultiplication n' n' n') =
      Tensor.matrixMultiplication n n n := by
    funext x y z
    simp [Tensor.pullback, Tensor.matrixMultiplication, f]
  rw [heq] at hpb
  exact exactRank_le hpb

/-- `R(u^j) ≤ R(u)^j`, from `matrixClass_mul` and `rank_mul_le`. -/
private theorem exactMatrixRank_pow_le_of_class (u j : ℕ) :
    exactMatrixRank (u ^ j) ≤ exactMatrixRank u ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := rank_mul_le (matrixClass (u ^ j)) (matrixClass u)
    rw [← matrixClass_mul, rank_matrixClass, rank_matrixClass, rank_matrixClass,
      ← pow_succ] at h
    rw [pow_succ]
    exact h.trans (Nat.mul_le_mul_right _ ih)

/-- Exponent slack: for `τ > ν` there is a fixed `u ≥ 2` with `R(n) ≤ (u n)^τ` for all `n ≥ 1`. -/
theorem exactMatrixRank_le_of_slack {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ u : ℕ, 2 ≤ u ∧ ∀ n : ℕ, 1 ≤ n → (exactMatrixRank n : ℝ) ≤ ((u : ℝ) * n) ^ τ := by
  obtain ⟨u, hu, huR⟩ := exists_exactMatrixRank_lt_rpow hτ
  refine ⟨u, hu, fun n hn => ?_⟩
  have hτpos : 0 < τ :=
    lt_of_lt_of_le (by norm_num) (exactRankExponent_lower.trans hτ.le)
  have hlt : n < u ^ (Nat.log u n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hle : u ^ (Nat.log u n + 1) ≤ u * n := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left u (Nat.pow_log_le_self u (by omega))
  have hR : exactMatrixRank n ≤ exactMatrixRank u ^ (Nat.log u n + 1) :=
    (exactMatrixRank_mono hlt.le).trans (exactMatrixRank_pow_le_of_class u _)
  calc (exactMatrixRank n : ℝ) ≤ (exactMatrixRank u : ℝ) ^ (Nat.log u n + 1) := by
        exact_mod_cast hR
    _ ≤ ((u : ℝ) ^ τ) ^ (Nat.log u n + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) huR.le _
    _ = ((u : ℝ) ^ (Nat.log u n + 1)) ^ τ := Real.rpow_pow_comm (Nat.cast_nonneg u) τ _
    _ ≤ ((u : ℝ) * n) ^ τ := by
        apply Real.rpow_le_rpow (by positivity) _ hτpos.le
        exact_mod_cast hle

/-- For every `τ > ν`: `ν β ≤ 90 log 3 + 68 τ log 2` (the limit `m → ∞` of
`exponent_le_logb` with the size bounds). -/
theorem exponent_mul_beta_le {τ : ℝ} (hτ : exactRankExponent < τ) :
    exactRankExponent * β ≤ 90 * Real.log 3 + 68 * τ * Real.log 2 := by
  set ν := exactRankExponent
  have hν : (2 : ℝ) ≤ ν := exactRankExponent_lower
  obtain ⟨u, hu, hslack⟩ := exactMatrixRank_le_of_slack hτ
  have hu0 : (0 : ℝ) < u := by
    have : 0 < u := by omega
    exact_mod_cast this
  have key : ∀ m : ℕ, 1 ≤ m →
      ν * β ≤ 90 * Real.log 3 + 68 * τ * Real.log 2 +
        ((258 * Real.log 5 + τ * Real.log u + 276 * ν) / (210 * m) +
          276 * ν * (Real.log (210 * m + 1) / (210 * m))) := by
    intro m hm
    have hmpos : (0 : ℝ) < 210 * m := by positivity
    -- (a) the exponent bound at this unit size
    have hB2 : (2 : ℝ) ≤ (B m : ℝ) := by exact_mod_cast two_le_B hm
    have hlogB : 0 < Real.log (B m : ℝ) := Real.log_pos (by linarith)
    have ha : ν * Real.log (B m : ℝ) ≤ Real.log (rank (L m) : ℝ) := by
      have h := exponent_le_logb hm
      rw [Real.logb, le_div_iff₀ hlogB] at h
      exact h
    have hr : (0 : ℝ) < (rank (L m) : ℝ) := by
      have hne : rank (L m) ≠ 0 := by
        intro h0
        have h0' : Real.log (rank (L m) : ℝ) = 0 := by rw [h0, Nat.cast_zero, Real.log_zero]
        have hpos : 0 < ν * Real.log (B m : ℝ) := mul_pos (by linarith) hlogB
        linarith only [h0', hpos, ha]
      exact_mod_cast Nat.pos_of_ne_zero hne
    -- (b) the size of the source
    have hRpos : 0 < exactMatrixRank (2 ^ (68 * (210 * m))) := exactMatrixRank_pos (by positivity)
    have hR : (0 : ℝ) < (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ) := by exact_mod_cast hRpos
    have hb : Real.log (rank (L m) : ℝ) ≤
        258 * Real.log 5 + (15 * (210 * m) : ℝ) * (6 * Real.log 3) +
          Real.log (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ) := by
      have h' : (rank (L m) : ℝ) ≤ (5 : ℝ) ^ 258 * (729 : ℝ) ^ (15 * (210 * m)) *
          (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ) := by exact_mod_cast rank_L_le m
      have h729 : Real.log 729 = 6 * Real.log 3 := by
        rw [show (729 : ℝ) = 3 ^ 6 by norm_num, Real.log_pow]
        push_cast
        ring
      calc Real.log (rank (L m) : ℝ)
          ≤ Real.log ((5 : ℝ) ^ 258 * (729 : ℝ) ^ (15 * (210 * m)) *
              (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ)) := Real.log_le_log hr h'
        _ = 258 * Real.log 5 + (15 * (210 * m) : ℝ) * (6 * Real.log 3) +
              Real.log (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ) := by
          rw [Real.log_mul (by positivity) hR.ne', Real.log_mul (by positivity) (by positivity),
            Real.log_pow, Real.log_pow, h729]
          push_cast
          ring
    -- (c) the slack bound on the matrix factor
    have hc : Real.log (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ) ≤
        τ * (Real.log u + (68 * (210 * m) : ℝ) * Real.log 2) := by
      have h := hslack (2 ^ (68 * (210 * m))) Nat.one_le_two_pow
      have hx : (0 : ℝ) < (u : ℝ) * ((2 ^ (68 * (210 * m)) : ℕ) : ℝ) := by positivity
      calc Real.log (exactMatrixRank (2 ^ (68 * (210 * m))) : ℝ)
          ≤ Real.log (((u : ℝ) * ((2 ^ (68 * (210 * m)) : ℕ) : ℝ)) ^ τ) := Real.log_le_log hR h
        _ = τ * (Real.log u + (68 * (210 * m) : ℝ) * Real.log 2) := by
          rw [Real.log_rpow hx, Real.log_mul hu0.ne' (by positivity), Nat.cast_pow, Real.log_pow]
          push_cast
          ring
    -- (d) the size of the target
    have hd := log_B_ge hm
    have hmul : ν * ((210 * m : ℝ) * β - 276 * (1 + Real.log (210 * m + 1))) ≤
        ν * Real.log (B m : ℝ) := mul_le_mul_of_nonneg_left hd (by linarith)
    have hsum : (ν * β - (90 * Real.log 3 + 68 * τ * Real.log 2)) * (210 * m) ≤
        (258 * Real.log 5 + τ * Real.log u + 276 * ν) + 276 * ν * Real.log (210 * m + 1) := by
      linarith [hmul, ha, hb, hc]
    have hdiv : ν * β - (90 * Real.log 3 + 68 * τ * Real.log 2) ≤
        ((258 * Real.log 5 + τ * Real.log u + 276 * ν) + 276 * ν * Real.log (210 * m + 1)) /
          (210 * m) := (le_div_iff₀ hmpos).2 hsum
    have e : (258 * Real.log 5 + τ * Real.log u + 276 * ν) / (210 * m) +
        276 * ν * (Real.log (210 * m + 1) / (210 * m)) =
        ((258 * Real.log 5 + τ * Real.log u + 276 * ν) + 276 * ν * Real.log (210 * m + 1)) /
          (210 * m) := by
      field_simp
    linarith
  -- the error term tends to zero
  have h1 : Filter.Tendsto (fun m : ℕ => 210 * (m : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h2 : Filter.Tendsto (fun m : ℕ => (258 * Real.log 5 + τ * Real.log u + 276 * ν) /
      (210 * (m : ℝ))) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h1
  have h3 : Filter.Tendsto (fun m : ℕ => Real.log (210 * m + 1) / (210 * (m : ℝ)))
      Filter.atTop (nhds 0) := by
    have h4 : Filter.Tendsto (fun m : ℕ => 210 * (m : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 h1
    have h5 := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp h4
    refine h5.congr (fun m => ?_)
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have h6 := (h2.add (h3.const_mul (276 * ν))).const_add (90 * Real.log 3 + 68 * τ * Real.log 2)
  rw [mul_zero, add_zero, add_zero] at h6
  exact ge_of_tendsto h6 (Filter.eventually_atTop.2 ⟨1, key⟩)

/-- The explicit `a₀ = 2` construction bounds the exact-rank exponent by
`90 log 3 / (β − 68 log 2) ≈ 2.7375`. -/
theorem exactRankExponent_le_primal_two :
    exactRankExponent ≤ 90 * Real.log 3 / (β - 68 * Real.log 2) := by
  have hpos := beta_sub_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  have h : exactRankExponent * β ≤ 90 * Real.log 3 + 68 * exactRankExponent * Real.log 2 := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hδ : 0 < ε / (68 * Real.log 2) := by positivity
    have h := exponent_mul_beta_le (τ := exactRankExponent + ε / (68 * Real.log 2)) (by linarith)
    have e : 68 * (exactRankExponent + ε / (68 * Real.log 2)) * Real.log 2 =
        68 * exactRankExponent * Real.log 2 + ε := by
      field_simp
    linarith
  linarith

end Two

end Primal

end

end OAI
