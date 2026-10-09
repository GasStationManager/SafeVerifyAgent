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
  sorry

theorem rank_pow_le (c : TensorClass) (n : ℕ) : rank (c ^ n) ≤ rank c ^ n := by
  sorry

theorem natCast_ne_zero_class {n : ℕ} (hn : 0 < n) : (n : TensorClass) ≠ 0 := by
  sorry

theorem mul_ne_zero_class {c d : TensorClass} (hc : c ≠ 0) (hd : d ≠ 0) : c * d ≠ 0 := by
  sorry

/-- From a catalytic degeneration `A ⊗ L ⇝ A ⊗ T_b`, Bini interpolation and removal of the
catalyst give `ν ≤ log_b (rank L)`. -/
theorem exactRankExponent_le_of_catalytic {A L : TensorClass} {b : ℕ} (hA : A ≠ 0) (hb : 2 ≤ b)
    (h : DegClass (A * L) (A * matrixClass b)) :
    exactRankExponent ≤ Real.logb b (rank L) := by
  sorry

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
  sorry

theorem Cat_ne_zero (m : ℕ) : Cat m ≠ 0 := by
  sorry

theorem two_le_B {m : ℕ} (hm : 1 ≤ m) : 2 ≤ B m := by
  sorry

/-- The exponent bound at each unit size, before the bootstrap. -/
theorem exponent_le_logb {m : ℕ} (hm : 1 ≤ m) :
    exactRankExponent ≤ Real.logb (B m) (rank (L m)) :=
  exactRankExponent_le_of_catalytic (Cat_ne_zero m) (two_le_B hm) (two_cat_degeneration m)

/-! ### Sizes -/

theorem rank_L_le (m : ℕ) :
    rank (L m) ≤ 5 ^ 258 * 729 ^ (15 * (210 * m)) * exactMatrixRank (2 ^ (68 * (210 * m))) := by
  sorry

/-- Binary entropy. -/
def Hb (p : ℝ) : ℝ := -(p * Real.log p) - (1 - p) * Real.log (1 - p)

theorem log_M₁_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * Hb (7 / 10) - 3 * (1 + Real.log (210 * m + 1)) ≤ Real.log (M₁ m) := by
  sorry

theorem log_M₂_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * Hb (9 / 14) - 3 * (1 + Real.log (210 * m + 1)) ≤ Real.log (M₂ m) := by
  sorry

theorem log_M₃_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * Real.log 3 - 4 * (1 + Real.log (210 * m + 1)) ≤ Real.log (M₃ m) := by
  sorry

/-- The growth rate of `log B_N / N`. -/
def β : ℝ := 30 * Real.log 2 + 40 * Hb (7 / 10) + 28 * Hb (9 / 14) + 18 * Real.log 3

theorem log_B_ge {m : ℕ} (hm : 1 ≤ m) :
    (210 * m : ℝ) * β - 276 * (1 + Real.log (210 * m + 1)) ≤ Real.log (B m) := by
  sorry

theorem beta_sub_pos : 0 < β - 68 * Real.log 2 := by
  sorry

/-! ### The bootstrap -/

/-- Monotonicity of the exact matrix rank in the dimension. -/
theorem exactMatrixRank_mono {n n' : ℕ} (h : n ≤ n') : exactMatrixRank n ≤ exactMatrixRank n' := by
  sorry

/-- Exponent slack: for `τ > ν` there is a fixed `u ≥ 2` with `R(n) ≤ (u n)^τ` for all `n ≥ 1`. -/
theorem exactMatrixRank_le_of_slack {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ u : ℕ, 2 ≤ u ∧ ∀ n : ℕ, 1 ≤ n → (exactMatrixRank n : ℝ) ≤ ((u : ℝ) * n) ^ τ := by
  sorry

/-- For every `τ > ν`: `ν β ≤ 90 log 3 + 68 τ log 2` (the limit `m → ∞` of
`exponent_le_logb` with the size bounds). -/
theorem exponent_mul_beta_le {τ : ℝ} (hτ : exactRankExponent < τ) :
    exactRankExponent * β ≤ 90 * Real.log 3 + 68 * τ * Real.log 2 := by
  sorry

/-- The explicit `a₀ = 2` construction bounds the exact-rank exponent by
`90 log 3 / (β − 68 log 2) ≈ 2.7375`. -/
theorem exactRankExponent_le_primal_two :
    exactRankExponent ≤ 90 * Real.log 3 / (β - 68 * Real.log 2) := by
  sorry

end Two

end Primal

end

end OAI
