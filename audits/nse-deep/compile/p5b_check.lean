import NavierStokes.StressAlgebra

/-! P5b VERIFICATION -- are the nonvanishing guards in StressAlgebra.lean actually needed?

The audit claimed, by hand re-derivation under Mathlib's `x/0 = 0`, that:
  * `stressFree_angular_lag_algebra` (:317) does NOT need `hphi : phi <> 0`
  * `angular_stress_coefficient`     (:339) does NOT need `hR : R <> 0` or `hL : L <> 0`
These restate each identity with those hypotheses REMOVED. If they compile, the claim is verified by the
kernel rather than by hand. Kept outside the artifact tree; NSE is never modified. -/

namespace P5BCheck
open NavierStokes.StressAlgebra

-- (1) `hphi` removed entirely.
theorem lag_no_hphi (x L phi phix phixx : ℝ) :
    x * (-2 * L * (phixx * phi - phix ^ 2) / phi ^ 2) +
      (2 + x * phix / phi) * (-2 * L * phix / phi) =
      -2 * L * (x * phixx + 2 * phix) / phi := by
  rcases eq_or_ne phi 0 with h | h
  · subst h; simp
  · field_simp; ring

-- (2) `hR` and `hL` both removed; only `hE` retained.
theorem angular_no_hR_hL (x R E L Qs Ex : ℝ) (hE : E ≠ 0) :
    (E / R) * (x * Qs / L - (1 - 2 * x * Ex / E)) =
      (E / R) * (x * Qs / L) + (2 * x * Ex - E) / R := by
  rcases eq_or_ne R 0 with hR | hR
  · subst hR; simp
  · field_simp; ring

end P5BCheck
