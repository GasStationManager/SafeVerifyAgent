import NavierStokes.Flatness
import NavierStokes.PulseCovariance

/-! P8 + junk-value VERIFICATION, by elaboration rather than by reading.
    Kept outside the artifact tree; NSE is never modified. -/

namespace VacuityCheck
open Filter

-- P8(a): `PowerFlat` has no `[NeBot l]`, so at `l = bot` it holds for ANY f, with C = 0.
-- If this compiles, every flatness claim is vacuously true at the bottom filter.
theorem powerFlat_bot_any {alpha : Type} (q f : alpha → ℝ) :
    NavierStokes.Flatness.PowerFlat (⊥ : Filter alpha) q f := by
  intro n
  exact ⟨0, le_refl 0, by simp⟩

-- Junk-value: `integral_gaussian_scaled` claims  INT gaussian b m r = r * sqrt (pi / b),
-- with `hr : 0 < r` but NO constraint on b. At b = 0 the audit claimed BOTH sides are 0,
-- via two independent junk values (a non-integrable integrand, and sqrt of pi/0).
-- (i) the right-hand side collapses:
theorem rhs_zero_at_b_zero (r : ℝ) : r * Real.sqrt (Real.pi / 0) = 0 := by
  simp
-- (ii) and the same for every b < 0, since sqrt of a negative is 0:
theorem rhs_zero_of_b_neg (r b : ℝ) (hb : b < 0) : r * Real.sqrt (Real.pi / b) = 0 := by
  have : Real.pi / b < 0 := div_neg_of_pos_of_neg Real.pi_pos hb
  simp [Real.sqrt_eq_zero_of_nonpos this.le]

end VacuityCheck
