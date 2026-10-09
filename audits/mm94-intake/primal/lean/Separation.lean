import Audit.Primal.Deg
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic

set_option linter.unusedSectionVars false

/-!
# Proposition 3.1 as a degree-tracked degeneration (audit, not part of the artifact)

The artifact proves the finite separation (`finiteSeparation_degeneratesTo`) only as a
topological closure statement, by evaluating `separationPolynomial` at every `t ≠ 0`.  The
primal construction needs the same degeneration as a `PolynomialRestrictionDegeneration`,
whose leg maps must be polynomials.  The artifact's leg maps carry integer (possibly negative)
weights `t ^ w`; shifting each leg by a constant makes every exponent nonnegative, and the
shifts add to the order of the degeneration.

Shifts: none on the first leg (`firstWeight g = g ^ 2 ≥ 0`), `M (M - 1)` on the second
(`secondWeight h u = h u - h ^ 2 ≥ -M (M - 1)` for `1 ≤ h, u ≤ M`), `M ^ 2` on the third
(`thirdWeight h v = -h v ≥ -M ^ 2`).  The restricted polynomial tensor is then exactly
`X ^ (2 M ^ 2 - M) * separationPolynomial`, so `vanishes` and `leading` follow from the
artifact's `separationPolynomial_coeff_zero`.
-/

namespace OAI

open MatrixMultiplication.Foundation
open MatrixMultiplication.AuxiliarySeparation

noncomputable section

namespace Primal

variable {M : ℕ} {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The shift on the second leg. -/
def shiftY (M : ℕ) : ℤ := (M : ℤ) * ((M : ℤ) - 1)

/-- The shift on the third leg. -/
def shiftZ (M : ℕ) : ℤ := (M : ℤ) ^ 2

/-- The total shift, which is the order of the degeneration. -/
def shiftTotal (M : ℕ) : ℕ := 2 * M ^ 2 - M

theorem shiftTotal_eq (M : ℕ) : (shiftTotal M : ℤ) = shiftY M + shiftZ M := by
  unfold shiftTotal shiftY shiftZ
  have h : M ≤ 2 * M ^ 2 := by
    have := Nat.le_mul_self M
    nlinarith
  push_cast [Nat.cast_sub h]
  ring

/-! ### Nonnegativity and size of the shifted weights on the sector range -/

theorem firstWeight_nonneg (g : ℤ) : 0 ≤ firstWeight g := by
  unfold firstWeight
  exact sq_nonneg g

theorem firstWeight_le {g : ℤ} (hg : 1 ≤ g ∧ g ≤ M) : firstWeight g ≤ (M : ℤ) ^ 2 := by
  unfold firstWeight
  nlinarith [hg.1, hg.2]

theorem secondWeight_shift_nonneg {h u : ℤ} (hh : 1 ≤ h ∧ h ≤ M) (hu : 1 ≤ u ∧ u ≤ M) :
    0 ≤ secondWeight h u + shiftY M := by
  unfold secondWeight shiftY
  nlinarith [mul_nonneg (sub_nonneg.2 hh.1) (sub_nonneg.2 hu.1),
    mul_nonneg (sub_nonneg.2 hh.2) (sub_nonneg.2 hh.1), sq_nonneg ((M : ℤ) - h)]

theorem secondWeight_shift_le {h u : ℤ} (hh : 1 ≤ h ∧ h ≤ M) (hu : 1 ≤ u ∧ u ≤ M) :
    secondWeight h u + shiftY M ≤ 2 * (M : ℤ) ^ 2 := by
  unfold secondWeight shiftY
  nlinarith [mul_nonneg (sub_nonneg.2 hh.2) (sub_nonneg.2 hu.2),
    mul_nonneg (sub_nonneg.2 hh.1) (sub_nonneg.2 hu.2),
    mul_nonneg (sub_nonneg.2 hh.2) (sub_nonneg.2 hu.1)]

theorem thirdWeight_shift_nonneg {h v : ℤ} (hh : 1 ≤ h ∧ h ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    0 ≤ thirdWeight h v + shiftZ M := by
  unfold thirdWeight shiftZ
  nlinarith [mul_nonneg (sub_nonneg.2 hh.2) (sub_nonneg.2 hv.2),
    mul_nonneg (sub_nonneg.2 hh.1) (sub_nonneg.2 hv.2),
    mul_nonneg (sub_nonneg.2 hh.2) (sub_nonneg.2 hv.1)]

theorem thirdWeight_shift_le {h v : ℤ} (hh : 1 ≤ h ∧ h ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    thirdWeight h v + shiftZ M ≤ (M : ℤ) ^ 2 := by
  unfold thirdWeight shiftZ
  nlinarith [mul_nonneg (sub_nonneg.2 hh.1) (sub_nonneg.2 hv.1)]

/-! ### The shifted polynomial leg maps -/

/-- The first leg map: the Fourier map times `X ^ (g ^ 2)`. -/
def shiftedFirstMap (ζ : ℂ) (x : X × Fin M) (r : Fin (5 * M) × X) : Polynomial ℂ :=
  Polynomial.X ^ (firstWeight (sectorNumber x.2)).toNat *
    Polynomial.C (firstProjectionMap ζ x r)

/-- The second leg map, shifted by `M (M - 1)`. -/
def shiftedSecondMap (ζ : ℂ) (y : (Fin M × Y) × Fin M)
    (r : Fin (5 * M) × (Fin M × Y)) : Polynomial ℂ :=
  Polynomial.X ^ (secondWeight (sectorNumber y.1.1) (sectorNumber y.2) + shiftY M).toNat *
    Polynomial.C (secondProjectionMap ζ y r)

/-- The third leg map, shifted by `M ^ 2`. -/
def shiftedThirdMap (ζ : ℂ) (z : (Fin M × Z) × Fin M)
    (r : Fin (5 * M) × (Fin M × Z)) : Polynomial ℂ :=
  Polynomial.X ^ (thirdWeight (sectorNumber z.1.1) (sectorNumber z.2) + shiftZ M).toNat *
    Polynomial.C (thirdProjectionMap ζ z r)

/-- A monomial `X ^ n * C a` has degree at most any `m ≥ n`. -/
private theorem degree_X_pow_mul_C_le {n m : ℕ} (a : ℂ) (h : n ≤ m) :
    (Polynomial.X ^ n * Polynomial.C a).degree ≤ (m : WithBot ℕ) := by
  rw [mul_comm]
  exact (Polynomial.degree_C_mul_X_pow_le n a).trans (by exact_mod_cast h)

theorem shiftedFirstMap_degree (ζ : ℂ) (x : X × Fin M) (r : Fin (5 * M) × X) :
    (shiftedFirstMap ζ x r).degree ≤ (M ^ 2 : ℕ) := by
  unfold shiftedFirstMap
  refine degree_X_pow_mul_C_le _ (Int.toNat_le.2 ?_)
  push_cast
  exact firstWeight_le (sectorNumber_bounds x.2)

theorem shiftedSecondMap_degree (ζ : ℂ) (y : (Fin M × Y) × Fin M)
    (r : Fin (5 * M) × (Fin M × Y)) :
    (shiftedSecondMap ζ y r).degree ≤ (2 * M ^ 2 : ℕ) := by
  unfold shiftedSecondMap
  refine degree_X_pow_mul_C_le _ (Int.toNat_le.2 ?_)
  push_cast
  exact secondWeight_shift_le (sectorNumber_bounds y.1.1) (sectorNumber_bounds y.2)

theorem shiftedThirdMap_degree (ζ : ℂ) (z : (Fin M × Z) × Fin M)
    (r : Fin (5 * M) × (Fin M × Z)) :
    (shiftedThirdMap ζ z r).degree ≤ (M ^ 2 : ℕ) := by
  unfold shiftedThirdMap
  refine degree_X_pow_mul_C_le _ (Int.toNat_le.2 ?_)
  push_cast
  exact thirdWeight_shift_le (sectorNumber_bounds z.1.1) (sectorNumber_bounds z.2)

/-! ### Evaluation at a nonzero parameter recovers the artifact's leg maps -/

theorem shiftedFirstMap_eval (ζ : ℂ) (x : X × Fin M) (r : Fin (5 * M) × X) (t : ℂ) :
    (shiftedFirstMap ζ x r).eval t = firstSeparationMap ζ t x r := by
  simp only [shiftedFirstMap, firstSeparationMap, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← zpow_natCast, Int.toNat_of_nonneg (firstWeight_nonneg _)]

theorem shiftedSecondMap_eval (ζ : ℂ) (y : (Fin M × Y) × Fin M)
    (r : Fin (5 * M) × (Fin M × Y)) {t : ℂ} (ht : t ≠ 0) :
    (shiftedSecondMap ζ y r).eval t = t ^ shiftY M * secondSeparationMap ζ t y r := by
  simp only [shiftedSecondMap, secondSeparationMap, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← zpow_natCast, Int.toNat_of_nonneg (secondWeight_shift_nonneg
    (sectorNumber_bounds y.1.1) (sectorNumber_bounds y.2)), zpow_add₀ ht]
  ring

theorem shiftedThirdMap_eval (ζ : ℂ) (z : (Fin M × Z) × Fin M)
    (r : Fin (5 * M) × (Fin M × Z)) {t : ℂ} (ht : t ≠ 0) :
    (shiftedThirdMap ζ z r).eval t = t ^ shiftZ M * thirdSeparationMap ζ t z r := by
  simp only [shiftedThirdMap, thirdSeparationMap, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← zpow_natCast, Int.toNat_of_nonneg (thirdWeight_shift_nonneg
    (sectorNumber_bounds z.1.1) (sectorNumber_bounds z.2)), zpow_add₀ ht]
  ring

/-- Evaluating a restriction of a constant-coefficient polynomial tensor is the restriction by
the evaluated maps. -/
theorem eval_restrict_C {X' Y' Z' : Type*}
    (A : X' → X → Polynomial ℂ) (B : Y' → Y → Polynomial ℂ) (C : Z' → Z → Polynomial ℂ)
    (T : Tensor ℂ X Y Z) (x : X') (y : Y') (z : Z') (t : ℂ) :
    (Tensor.restrict A B C (fun x y z => Polynomial.C (T x y z)) x y z).eval t =
      Tensor.restrict (fun x' x => (A x' x).eval t) (fun y' y => (B y' y).eval t)
        (fun z' z => (C z' z).eval t) T x y z := by
  simp only [Tensor.restrict, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

/-- Scalar factors on the leg maps come out of a restriction. -/
theorem restrict_scalar_legs {X' Y' Z' : Type*}
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ)
    (s : X' → ℂ) (u : Y' → ℂ) (v : Z' → ℂ) (T : Tensor ℂ X Y Z) (x : X') (y : Y') (z : Z') :
    Tensor.restrict (fun x' x => s x' * A x' x) (fun y' y => u y' * B y' y)
        (fun z' z => v z' * C z' z) T x y z =
      s x * u y * v z * Tensor.restrict A B C T x y z := by
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The key identity: the shifted restriction is `X ^ shiftTotal M` times the artifact's
separation polynomial.  Both sides are polynomials agreeing at every `t ≠ 0`. -/
theorem shifted_restrict_eq {ζ : ℂ} (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (B : Fin M → Tensor ℂ X Y Z)
    (x : X × Fin M) (y : (Fin M × Y) × Fin M) (z : (Fin M × Z) × Fin M) :
    Tensor.restrict (shiftedFirstMap ζ) (shiftedSecondMap ζ) (shiftedThirdMap ζ)
        (fun x y z => Polynomial.C
          (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B) x y z)) x y z =
      Polynomial.X ^ shiftTotal M * separationPolynomial ζ B x y z := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
  intro t ht
  have ht0 : t ≠ 0 := ht
  show Polynomial.eval t _ = Polynomial.eval t _
  rw [eval_restrict_C]
  have h1 : (fun (x' : X × Fin M) (r : Fin (5 * M) × X) => (shiftedFirstMap ζ x' r).eval t) =
      fun x' r => (fun _ => (1 : ℂ)) x' * firstSeparationMap ζ t x' r := by
    funext x' r
    rw [shiftedFirstMap_eval, one_mul]
  have h2 : (fun (y' : (Fin M × Y) × Fin M) (r : Fin (5 * M) × (Fin M × Y)) =>
      (shiftedSecondMap ζ y' r).eval t) =
      fun y' r => (fun _ => t ^ shiftY M) y' * secondSeparationMap ζ t y' r := by
    funext y' r
    rw [shiftedSecondMap_eval ζ _ _ ht0]
  have h3 : (fun (z' : (Fin M × Z) × Fin M) (r : Fin (5 * M) × (Fin M × Z)) =>
      (shiftedThirdMap ζ z' r).eval t) =
      fun z' r => (fun _ => t ^ shiftZ M) z' * thirdSeparationMap ζ t z' r := by
    funext z' r
    rw [shiftedThirdMap_eval ζ _ _ ht0]
  have hsep : (separationPolynomial ζ B x y z).eval t =
      Tensor.restrict (firstSeparationMap ζ t) (secondSeparationMap ζ t)
        (thirdSeparationMap ζ t)
        (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B)) x y z :=
    congrFun (congrFun (congrFun (separationPolynomial_eval hM hζ B t ht0) x) y) z
  rw [h1, h2, h3, restrict_scalar_legs, ← hsep, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, ← zpow_natCast, shiftTotal_eq, zpow_add₀ ht0]
  ring

/-- Proposition 3.1 as a polynomial restriction degeneration of order `2 M ^ 2 - M`. -/
def separationDegeneration {ζ : ℂ} (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.PolynomialRestrictionDegeneration
      (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B))
      (separationTarget B) (shiftTotal M) (M ^ 2) (2 * M ^ 2) (M ^ 2) where
  leftMap := shiftedFirstMap ζ
  middleMap := shiftedSecondMap ζ
  rightMap := shiftedThirdMap ζ
  left_degree := shiftedFirstMap_degree ζ
  middle_degree := shiftedSecondMap_degree ζ
  right_degree := shiftedThirdMap_degree ζ
  vanishes := by
    intro x y z j hj
    rw [shifted_restrict_eq hM hζ B x y z, Polynomial.coeff_X_pow_mul']
    exact ite_eq_right (Nat.not_le_of_lt hj)
  leading := by
    intro x y z
    rw [shifted_restrict_eq hM hζ B x y z, Polynomial.coeff_X_pow_mul',
      ite_eq_left le_rfl, Nat.sub_self]
    exact congrFun (congrFun (congrFun (separationPolynomial_coeff_zero hM hζ B) x) y) z

/-- `5 M` copies of the shared-first tensor degenerate, with tracked degrees, to the separated
target. -/
theorem deg_separation (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    Deg (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B))
      (separationTarget B) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (5 * M : ℕ))
  have hζ : IsPrimitiveRoot ζ (5 * M) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  exact ⟨_, _, _, _, ⟨separationDegeneration hM hζ B⟩⟩

end Primal

end

end OAI
