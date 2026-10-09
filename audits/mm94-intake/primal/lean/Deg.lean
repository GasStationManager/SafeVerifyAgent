import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialWitnessProduct
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialRestriction
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialExecutionSymmetry
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

set_option linter.unusedSectionVars false

/-!
# Degree-tracked degeneration and approximation (audit, not part of the artifact)

`Deg T U` says some `PolynomialRestrictionDegeneration` from `T` to `U` exists (degrees
existential); `Approx T ρ` says some `PolynomialApproximation` of `T` with rank `ρ` exists.
Everything here is on top of the artifact's definitions; nothing in the artifact is changed.
-/

namespace OAI

open MatrixMultiplication.Foundation

noncomputable section

namespace Primal

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [Fintype X''] [Fintype Y''] [Fintype Z'']

/-- Degree-tracked degeneration: a polynomial restriction degeneration exists. -/
def Deg (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') : Prop :=
  ∃ k Lx Ly Lz : ℕ, Nonempty (Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)

/-- Degree-tracked approximation of rank at most `ρ`. -/
def Approx (T : Tensor ℂ X Y Z) (ρ : ℕ) : Prop :=
  ∃ d D : ℕ, Nonempty (Tensor.PolynomialApproximation T ρ d D)

/-- Exchange the second and third legs. -/
def swapYZ {K : Type*} [CommSemiring K] (T : Tensor K X Y Z) : Tensor K X Z Y :=
  fun x z y => T x y z

namespace Approx

theorem of_rankAtMost {T : Tensor ℂ X Y Z} {ρ : ℕ} (h : Tensor.RankAtMost T ρ) :
    Approx T ρ :=
  ⟨0, 0, ⟨Tensor.PolynomialApproximation.ofRankAtMost T ρ h⟩⟩

theorem product {T : Tensor ℂ X Y Z} {S : Tensor ℂ X' Y' Z'} {ρ σ : ℕ}
    (hT : Approx T ρ) (hS : Approx S σ) : Approx (Tensor.product T S) (ρ * σ) := by
  obtain ⟨d, D, ⟨A⟩⟩ := hT
  obtain ⟨e, E, ⟨B⟩⟩ := hS
  exact ⟨d + e, D + E, ⟨A.product B⟩⟩

theorem pullback {T : Tensor ℂ X Y Z} {ρ : ℕ} (hT : Approx T ρ)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    Approx (Tensor.pullback fx fy fz T) ρ := by
  obtain ⟨d, D, ⟨A⟩⟩ := hT
  exact ⟨d, D, ⟨A.pullback fx fy fz⟩⟩

theorem restrict {T : Tensor ℂ X Y Z} {ρ : ℕ} (hT : Approx T ρ)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    Approx (Tensor.restrict A B C T) ρ := by
  obtain ⟨d, D, ⟨W⟩⟩ := hT
  exact ⟨d, D, ⟨W.restrict A B C⟩⟩

theorem cyclic {T : Tensor ℂ X Y Z} {ρ : ℕ} (hT : Approx T ρ) :
    Approx (Tensor.cyclic T) ρ := by
  obtain ⟨d, D, ⟨A⟩⟩ := hT
  exact ⟨d, D, ⟨A.cyclic⟩⟩

theorem power {T : Tensor ℂ X Y Z} {ρ : ℕ} (hT : Approx T ρ) (n : ℕ) :
    Approx (Tensor.power T n) (ρ ^ n) := by
  obtain ⟨d, D, ⟨A⟩⟩ := hT
  exact ⟨d * n, D * n, ⟨A.power n⟩⟩

/-- Bini's interpolation: every tensor power has rank bounded with linear overhead. -/
theorem rank_power {T : Tensor ℂ X Y Z} {ρ : ℕ} (hT : Approx T ρ) :
    ∃ D : ℕ, ∀ m : ℕ, Tensor.RankAtMost (Tensor.power T m) ((D * m + 1) * ρ ^ m) := by
  obtain ⟨d, D, ⟨A⟩⟩ := hT
  exact ⟨D, fun m => A.rank_power m⟩

/-- Rank bounds can be weakened (pad with zero simple tensors). -/
theorem mono {T : Tensor ℂ X Y Z} {ρ ρ' : ℕ} (hT : Approx T ρ) (h : ρ ≤ ρ') :
    Approx T ρ' := by
  obtain ⟨d, D, ⟨A⟩⟩ := hT
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hrank : Tensor.RankAtMost A.polynomial (ρ + m) := by
    obtain ⟨a, b, c, hP⟩ := A.rank_bound
    refine ⟨Fin.append a (fun _ _ => 0), Fin.append b (fun _ _ => 0),
      Fin.append c (fun _ _ => 0), ?_⟩
    rw [hP]
    funext x y z
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Tensor.rankOne,
      zero_mul, Finset.sum_const_zero, add_zero]
  exact ⟨d, D, ⟨{
    polynomial := A.polynomial
    rank_bound := hrank
    vanishes := A.vanishes
    leading := A.leading
    degree_bound := A.degree_bound }⟩⟩

end Approx

section DegenerationPower

variable {F : Type*} [Field F]

/-- Restricting a tensor power by coordinatewise product maps gives the tensor power of the
restriction. -/
theorem restrict_power_prodMaps {K : Type*} [CommSemiring K]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K) (P : Tensor K X Y Z) (n : ℕ) :
    Tensor.restrict (fun (a : Fin n → X') (b : Fin n → X) => ∏ i, A (a i) (b i))
        (fun (a : Fin n → Y') (b : Fin n → Y) => ∏ i, B (a i) (b i))
        (fun (a : Fin n → Z') (b : Fin n → Z) => ∏ i, C (a i) (b i))
        (Tensor.power P n) =
      Tensor.power (Tensor.restrict A B C P) n := by
  funext x' y' z'
  simp only [Tensor.restrict, Tensor.power, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- A product of `n` polynomials of degree at most `L` has degree at most `L * n`. -/
theorem degree_prod_fin_le {n L : ℕ} (p : Fin n → Polynomial F)
    (h : ∀ i, (p i).degree ≤ L) : (∏ i, p i).degree ≤ ((L * n : ℕ) : WithBot ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (∏ i, p i).natDegree ≤ ∑ i, (p i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin n, L :=
      Finset.sum_le_sum fun i _ => Polynomial.natDegree_le_of_degree_le (h i)
    _ = L * n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- Coordinatewise product maps turn a polynomial restriction degeneration of order `k`
into one of order `k * n` between the `n`-th tensor powers. -/
theorem polynomialRestrictionDegeneration_power {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'}
    {k Lx Ly Lz : ℕ} (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) (n : ℕ) :
    Nonempty (Tensor.PolynomialRestrictionDegeneration (Tensor.power T n) (Tensor.power U n)
      (k * n) (Lx * n) (Ly * n) (Lz * n)) := by
  -- Each base coefficient polynomial is `X ^ k` times a polynomial with constant term `U`.
  have hfac : ∀ (x' : X') (y' : Y') (z' : Z'), ∃ q : Polynomial F,
      Tensor.restrict L.leftMap L.middleMap L.rightMap
          (fun x y z => Polynomial.C (T x y z)) x' y' z' = Polynomial.X ^ k * q ∧
        q.coeff 0 = U x' y' z' := by
    intro x' y' z'
    obtain ⟨q, hq⟩ := Polynomial.X_pow_dvd_iff.mpr (L.vanishes x' y' z')
    refine ⟨q, hq, ?_⟩
    have hlead := L.leading x' y' z'
    rw [hq, Polynomial.coeff_X_pow_mul', ite_eq_left (Nat.le_refl k), Nat.sub_self] at hlead
    exact hlead
  choose q hq hq0 using hfac
  -- The restriction of the power is the power of the restriction, hence `X ^ (k * n)` times
  -- a product of polynomials with constant terms `U`.
  have hpow : ∀ (x' : Fin n → X') (y' : Fin n → Y') (z' : Fin n → Z'),
      Tensor.restrict (fun (a : Fin n → X') (b : Fin n → X) => ∏ i, L.leftMap (a i) (b i))
          (fun (a : Fin n → Y') (b : Fin n → Y) => ∏ i, L.middleMap (a i) (b i))
          (fun (a : Fin n → Z') (b : Fin n → Z) => ∏ i, L.rightMap (a i) (b i))
          (fun x y z => Polynomial.C (Tensor.power T n x y z)) x' y' z' =
        Polynomial.X ^ (k * n) * ∏ i, q (x' i) (y' i) (z' i) := by
    intro x' y' z'
    have hC : (fun (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) =>
        Polynomial.C (Tensor.power T n x y z)) =
        Tensor.power (fun x y z => Polynomial.C (T x y z)) n := by
      funext x y z
      simp only [Tensor.power, map_prod]
    rw [hC, restrict_power_prodMaps L.leftMap L.middleMap L.rightMap]
    simp only [Tensor.power, hq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_mul]
  exact ⟨{
    leftMap := fun x' x => ∏ i, L.leftMap (x' i) (x i)
    middleMap := fun y' y => ∏ i, L.middleMap (y' i) (y i)
    rightMap := fun z' z => ∏ i, L.rightMap (z' i) (z i)
    left_degree := fun x' x => degree_prod_fin_le _ fun i => L.left_degree (x' i) (x i)
    middle_degree := fun y' y => degree_prod_fin_le _ fun i => L.middle_degree (y' i) (y i)
    right_degree := fun z' z => degree_prod_fin_le _ fun i => L.right_degree (z' i) (z i)
    vanishes := by
      intro x' y' z' j hj
      rw [hpow x' y' z', Polynomial.coeff_X_pow_mul', ite_eq_right (Nat.not_le_of_lt hj)]
    leading := by
      intro x' y' z'
      rw [hpow x' y' z', Polynomial.coeff_X_pow_mul', ite_eq_left (Nat.le_refl (k * n)),
        Nat.sub_self, Polynomial.coeff_zero_prod]
      simp only [hq0, Tensor.power] }⟩

end DegenerationPower

namespace Deg

/-- A degeneration turns an approximation of its source into one of its target. -/
theorem toApprox {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U)
    {ρ : ℕ} (hT : Approx T ρ) : Approx U ρ := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  obtain ⟨d, D, ⟨W⟩⟩ := hT
  exact ⟨_, _, ⟨L.compose W⟩⟩

theorem refl (T : Tensor ℂ X Y Z) : Deg T T := by
  classical
  have hdeg : ∀ (p : Prop) [Decidable p],
      (if p then (1 : Polynomial ℂ) else 0).degree ≤ ((0 : ℕ) : WithBot ℕ) := by
    intro p _
    split_ifs
    · simpa only [Nat.cast_zero] using Polynomial.degree_one_le (R := ℂ)
    · simp only [Polynomial.degree_zero, bot_le]
  exact ⟨0, 0, 0, 0, ⟨{
    leftMap := fun x' x => if x = x' then 1 else 0
    middleMap := fun y' y => if y = y' then 1 else 0
    rightMap := fun z' z => if z = z' then 1 else 0
    left_degree := fun x' x => hdeg _
    middle_degree := fun y' y => hdeg _
    right_degree := fun z' z => hdeg _
    vanishes := fun x' y' z' j hj => absurd hj (Nat.not_lt_zero j)
    leading := fun x' y' z' => by
      rw [Tensor.restrict_identity]
      exact Polynomial.coeff_C_zero }⟩⟩

/-- Every restriction is a degeneration of order zero. -/
theorem of_restrict (T : Tensor ℂ X Y Z) (A : X' → X → ℂ) (B : Y' → Y → ℂ)
    (C : Z' → Z → ℂ) : Deg T (Tensor.restrict A B C T) := by
  refine ⟨0, 0, 0, 0, ⟨{
    leftMap := fun x' x => Polynomial.C (A x' x)
    middleMap := fun y' y => Polynomial.C (B y' y)
    rightMap := fun z' z => Polynomial.C (C z' z)
    left_degree := fun x' x => by
      simpa only [Nat.cast_zero] using Polynomial.degree_C_le (a := A x' x)
    middle_degree := fun y' y => by
      simpa only [Nat.cast_zero] using Polynomial.degree_C_le (a := B y' y)
    right_degree := fun z' z => by
      simpa only [Nat.cast_zero] using Polynomial.degree_C_le (a := C z' z)
    vanishes := fun x' y' z' j hj => absurd hj (Nat.not_lt_zero j)
    leading := fun x' y' z' => ?_ }⟩⟩
  change (Tensor.restrictPolynomial A B C (fun x y z => Polynomial.C (T x y z))
    x' y' z').coeff 0 = Tensor.restrict A B C T x' y' z'
  rw [Tensor.restrictPolynomial_coeff]
  simp only [Polynomial.coeff_C_zero]

theorem of_pullback (T : Tensor ℂ X Y Z) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    Deg T (Tensor.pullback fx fy fz T) := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact of_restrict T _ _ _

theorem of_eq {T : Tensor ℂ X Y Z} {U : Tensor ℂ X Y Z} (h : T = U) : Deg T U := by
  subst h
  exact refl T

/-- The base polynomial of a degeneration of order `k` factors as `X ^ k * q` with
`q(0)` the target entry. -/
private theorem exists_factor {F α β γ α' β' γ' : Type*} [Field F]
    [Fintype α] [Fintype β] [Fintype γ]
    {T : Tensor F α β γ} {U : Tensor F α' β' γ'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (a : α') (b : β') (c : γ') :
    ∃ q : Polynomial F,
      Tensor.restrict L.leftMap L.middleMap L.rightMap
          (fun x y z => Polynomial.C (T x y z)) a b c = Polynomial.X ^ k * q ∧
        q.coeff 0 = U a b c := by
  obtain ⟨q, hq⟩ := Polynomial.X_pow_dvd_iff.mpr (L.vanishes a b c)
  refine ⟨q, hq, ?_⟩
  have h := L.leading a b c
  rw [hq, Polynomial.coeff_X_pow_mul', ite_eq_left (le_refl k), Nat.sub_self] at h
  exact h

/-- Degree of a composite leg map `∑ b, M₂ c b * expand n (M₁ b a)`. -/
private theorem trans_map_degree {F : Type*} [Field F] {α β γ : Type*} [Fintype β]
    (M₂ : γ → β → Polynomial F) (M₁ : β → α → Polynomial F) (n d₁ d₂ : ℕ)
    (h₂ : ∀ c b, (M₂ c b).degree ≤ d₂) (h₁ : ∀ b a, (M₁ b a).degree ≤ d₁)
    (c : γ) (a : α) :
    (∑ b, M₂ c b * Polynomial.expand F n (M₁ b a)).degree ≤ ((d₂ + d₁ * n : ℕ) : WithBot ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b _
  apply Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_le_of_degree_le (h₂ c b))
  rw [Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right n (Polynomial.natDegree_le_of_degree_le (h₁ b a))

/-- The composite restriction of `T` is `X ^ (k₁ (k₂ + 1)) * N`, where `N` agrees with the
base polynomial of `L₂` up to order `k₂`. -/
private theorem trans_factor {F : Type*} [Field F]
    {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'} {V : Tensor F X'' Y'' Z''}
    {k₁ Lx₁ Ly₁ Lz₁ k₂ Lx₂ Ly₂ Lz₂ : ℕ}
    (L₁ : Tensor.PolynomialRestrictionDegeneration T U k₁ Lx₁ Ly₁ Lz₁)
    (L₂ : Tensor.PolynomialRestrictionDegeneration U V k₂ Lx₂ Ly₂ Lz₂)
    (x'' : X'') (y'' : Y'') (z'' : Z'') :
    ∃ N : Polynomial F,
      Tensor.restrict
          (fun x'' x => ∑ x', L₂.leftMap x'' x' *
            Polynomial.expand F (k₂ + 1) (L₁.leftMap x' x))
          (fun y'' y => ∑ y', L₂.middleMap y'' y' *
            Polynomial.expand F (k₂ + 1) (L₁.middleMap y' y))
          (fun z'' z => ∑ z', L₂.rightMap z'' z' *
            Polynomial.expand F (k₂ + 1) (L₁.rightMap z' z))
          (fun x y z => Polynomial.C (T x y z)) x'' y'' z'' =
        Polynomial.X ^ (k₁ * (k₂ + 1)) * N ∧
      ∀ j, j ≤ k₂ → N.coeff j =
        (Tensor.restrict L₂.leftMap L₂.middleMap L₂.rightMap
          (fun x y z => Polynomial.C (U x y z)) x'' y'' z'').coeff j := by
  choose Q hQ hQ0 using exists_factor L₁
  have hinner : Tensor.restrict
      (fun x' x => Polynomial.expand F (k₂ + 1) (L₁.leftMap x' x))
      (fun y' y => Polynomial.expand F (k₂ + 1) (L₁.middleMap y' y))
      (fun z' z => Polynomial.expand F (k₂ + 1) (L₁.rightMap z' z))
      (fun x y z => Polynomial.C (T x y z)) =
      fun x' y' z' => Polynomial.X ^ (k₁ * (k₂ + 1)) *
        Polynomial.expand F (k₂ + 1) (Q x' y' z') := by
    funext x' y' z'
    calc _ = Polynomial.expand F (k₂ + 1) (Tensor.restrict L₁.leftMap L₁.middleMap
          L₁.rightMap (fun x y z => Polynomial.C (T x y z)) x' y' z') := by
          simp only [Tensor.restrict, map_sum, map_mul, Polynomial.expand_C]
      _ = _ := by
          rw [hQ x' y' z', map_mul, map_pow, Polynomial.expand_X, ← pow_mul']
  refine ⟨Tensor.restrict L₂.leftMap L₂.middleMap L₂.rightMap
    (fun x' y' z' => Polynomial.expand F (k₂ + 1) (Q x' y' z')) x'' y'' z'', ?_, ?_⟩
  · calc _ = Tensor.restrict L₂.leftMap L₂.middleMap L₂.rightMap
          (fun x' y' z' => Polynomial.X ^ (k₁ * (k₂ + 1)) *
            Polynomial.expand F (k₂ + 1) (Q x' y' z')) x'' y'' z'' := by
          rw [← hinner, Tensor.restrict_restrict]
          rfl
      _ = _ := by rw [Tensor.restrict_scalar_mul]
  · intro j hj
    simp only [Tensor.restrict, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro x' _
    apply Finset.sum_congr rfl
    intro y' _
    apply Finset.sum_congr rfl
    intro z' _
    exact Tensor.coeff_mul_expand_eq_constant
      (L₂.leftMap x'' x' * L₂.middleMap y'' y' * L₂.rightMap z'' z')
      (Q x' y' z') (U x' y' z') (hQ0 x' y' z') k₂ j hj

/-- Composite of two degenerations: `L₂`'s maps after the `(k₂ + 1)`-expanded maps of `L₁`. -/
def transDegeneration {F : Type*} [Field F]
    {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'} {V : Tensor F X'' Y'' Z''}
    {k₁ Lx₁ Ly₁ Lz₁ k₂ Lx₂ Ly₂ Lz₂ : ℕ}
    (L₁ : Tensor.PolynomialRestrictionDegeneration T U k₁ Lx₁ Ly₁ Lz₁)
    (L₂ : Tensor.PolynomialRestrictionDegeneration U V k₂ Lx₂ Ly₂ Lz₂) :
    Tensor.PolynomialRestrictionDegeneration T V (k₁ * (k₂ + 1) + k₂)
      (Lx₂ + Lx₁ * (k₂ + 1)) (Ly₂ + Ly₁ * (k₂ + 1)) (Lz₂ + Lz₁ * (k₂ + 1)) where
  leftMap x'' x := ∑ x', L₂.leftMap x'' x' * Polynomial.expand F (k₂ + 1) (L₁.leftMap x' x)
  middleMap y'' y := ∑ y', L₂.middleMap y'' y' *
    Polynomial.expand F (k₂ + 1) (L₁.middleMap y' y)
  rightMap z'' z := ∑ z', L₂.rightMap z'' z' *
    Polynomial.expand F (k₂ + 1) (L₁.rightMap z' z)
  left_degree := trans_map_degree L₂.leftMap L₁.leftMap (k₂ + 1) Lx₁ Lx₂
    L₂.left_degree L₁.left_degree
  middle_degree := trans_map_degree L₂.middleMap L₁.middleMap (k₂ + 1) Ly₁ Ly₂
    L₂.middle_degree L₁.middle_degree
  right_degree := trans_map_degree L₂.rightMap L₁.rightMap (k₂ + 1) Lz₁ Lz₂
    L₂.right_degree L₁.right_degree
  vanishes := by
    intro x'' y'' z'' j hj
    obtain ⟨N, hN, hNc⟩ := trans_factor L₁ L₂ x'' y'' z''
    rw [hN, Polynomial.coeff_X_pow_mul']
    split_ifs with hdj
    · have hjk : j - k₁ * (k₂ + 1) < k₂ := by omega
      rw [hNc _ (Nat.le_of_lt hjk)]
      exact L₂.vanishes x'' y'' z'' _ hjk
    · rfl
  leading := by
    intro x'' y'' z''
    obtain ⟨N, hN, hNc⟩ := trans_factor L₁ L₂ x'' y'' z''
    rw [hN, Polynomial.coeff_X_pow_mul', ite_eq_left (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, hNc _ le_rfl]
    exact L₂.leading x'' y'' z''

private theorem mul_degree_le {F : Type*} [Field F] {p q : Polynomial F} {a b : ℕ}
    (hp : p.degree ≤ a) (hq : q.degree ≤ b) : (p * q).degree ≤ ((a + b : ℕ) : WithBot ℕ) :=
  Polynomial.degree_le_of_natDegree_le (Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_le_of_degree_le hp) (Polynomial.natDegree_le_of_degree_le hq))

/-- The restriction of a product by product maps is the product of the restrictions. -/
private theorem product_point_eq {F : Type*} [Field F] {U V W U' V' W' : Type*}
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor F X Y Z} {T' : Tensor F X' Y' Z'}
    {S : Tensor F U V W} {S' : Tensor F U' V' W'}
    {k Lx Ly Lz m Mx My Mz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T T' k Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' m Mx My Mz)
    (x : X' × U') (y : Y' × V') (z : Z' × W') :
    Tensor.restrict (fun (a : X' × U') (b : X × U) => L.leftMap a.1 b.1 * M.leftMap a.2 b.2)
        (fun (a : Y' × V') (b : Y × V) => L.middleMap a.1 b.1 * M.middleMap a.2 b.2)
        (fun (a : Z' × W') (b : Z × W) => L.rightMap a.1 b.1 * M.rightMap a.2 b.2)
        (fun a b c => Polynomial.C (Tensor.product T S a b c)) x y z =
      Tensor.restrict L.leftMap L.middleMap L.rightMap
          (fun a b c => Polynomial.C (T a b c)) x.1 y.1 z.1 *
        Tensor.restrict M.leftMap M.middleMap M.rightMap
          (fun a b c => Polynomial.C (S a b c)) x.2 y.2 z.2 := by
  have hconst : (fun a b c => Polynomial.C (Tensor.product T S a b c)) =
      Tensor.product (fun a b c => Polynomial.C (T a b c))
        (fun a b c => Polynomial.C (S a b c)) := by
    funext a b c
    exact map_mul Polynomial.C (T a.1 b.1 c.1) (S a.2 b.2 c.2)
  rw [hconst, Tensor.restrict_product L.leftMap L.middleMap L.rightMap
    M.leftMap M.middleMap M.rightMap]
  rfl

/-- Tensor product of two degenerations: orders and degrees add. -/
def productDegeneration {F : Type*} [Field F] {U V W U' V' W' : Type*}
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor F X Y Z} {T' : Tensor F X' Y' Z'}
    {S : Tensor F U V W} {S' : Tensor F U' V' W'}
    {k Lx Ly Lz m Mx My Mz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T T' k Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' m Mx My Mz) :
    Tensor.PolynomialRestrictionDegeneration (Tensor.product T S) (Tensor.product T' S')
      (k + m) (Lx + Mx) (Ly + My) (Lz + Mz) where
  leftMap a b := L.leftMap a.1 b.1 * M.leftMap a.2 b.2
  middleMap a b := L.middleMap a.1 b.1 * M.middleMap a.2 b.2
  rightMap a b := L.rightMap a.1 b.1 * M.rightMap a.2 b.2
  left_degree a b := mul_degree_le (L.left_degree a.1 b.1) (M.left_degree a.2 b.2)
  middle_degree a b := mul_degree_le (L.middle_degree a.1 b.1) (M.middle_degree a.2 b.2)
  right_degree a b := mul_degree_le (L.right_degree a.1 b.1) (M.right_degree a.2 b.2)
  vanishes := by
    intro x y z j hj
    obtain ⟨p, hp, -⟩ := exists_factor L x.1 y.1 z.1
    obtain ⟨q, hq, -⟩ := exists_factor M x.2 y.2 z.2
    rw [product_point_eq L M x y z, hp, hq, mul_mul_mul_comm, ← pow_add,
      Polynomial.coeff_X_pow_mul', ite_eq_right (Nat.not_le_of_lt hj)]
  leading := by
    intro x y z
    obtain ⟨p, hp, hp0⟩ := exists_factor L x.1 y.1 z.1
    obtain ⟨q, hq, hq0⟩ := exists_factor M x.2 y.2 z.2
    rw [product_point_eq L M x y z, hp, hq, mul_mul_mul_comm, ← pow_add,
      Polynomial.coeff_X_pow_mul', ite_eq_left (le_refl _), Nat.sub_self,
      Polynomial.mul_coeff_zero, hp0, hq0]
    rfl

/-- Composition of degenerations (orders compose as in `compose`). -/
theorem trans {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {V : Tensor ℂ X'' Y'' Z''}
    (hTU : Deg T U) (hUV : Deg U V) : Deg T V := by
  obtain ⟨k₁, Lx₁, Ly₁, Lz₁, ⟨L₁⟩⟩ := hTU
  obtain ⟨k₂, Lx₂, Ly₂, Lz₂, ⟨L₂⟩⟩ := hUV
  exact ⟨_, _, _, _, ⟨transDegeneration L₁ L₂⟩⟩

theorem product {U V W U' V' W' : Type*}
    [Fintype U] [Fintype V] [Fintype W] [Fintype U'] [Fintype V'] [Fintype W']
    {T : Tensor ℂ X Y Z} {T' : Tensor ℂ X' Y' Z'}
    {S : Tensor ℂ U V W} {S' : Tensor ℂ U' V' W'}
    (hT : Deg T T') (hS : Deg S S') :
    Deg (Tensor.product T S) (Tensor.product T' S') := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := hT
  obtain ⟨m, Mx, My, Mz, ⟨M⟩⟩ := hS
  exact ⟨_, _, _, _, ⟨productDegeneration L M⟩⟩

theorem cyclic {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U) :
    Deg (Tensor.cyclic T) (Tensor.cyclic U) := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  exact ⟨k, Ly, Lz, Lx, ⟨L.cyclic⟩⟩

theorem swapYZ {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U) :
    Deg (Primal.swapYZ T) (Primal.swapYZ U) := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  have hswap : ∀ (x' : X') (z' : Z') (y' : Y'),
      Tensor.restrict L.leftMap L.rightMap L.middleMap
          (fun x z y => Polynomial.C (Primal.swapYZ T x z y)) x' z' y' =
        Tensor.restrict L.leftMap L.middleMap L.rightMap
          (fun x y z => Polynomial.C (T x y z)) x' y' z' := by
    intro x' z' y'
    simp only [Tensor.restrict, Primal.swapYZ]
    apply Finset.sum_congr rfl
    intro x _
    refine Finset.sum_comm.trans ?_
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  exact ⟨k, Lx, Lz, Ly, ⟨{
    leftMap := L.leftMap
    middleMap := L.rightMap
    rightMap := L.middleMap
    left_degree := L.left_degree
    middle_degree := L.right_degree
    right_degree := L.middle_degree
    vanishes := fun x' z' y' j hj => by
      rw [hswap x' z' y']
      exact L.vanishes x' y' z' j hj
    leading := fun x' z' y' => by
      rw [hswap x' z' y']
      exact L.leading x' y' z' }⟩⟩

theorem power {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U) (n : ℕ) :
    Deg (Tensor.power T n) (Tensor.power U n) := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  exact ⟨k * n, Lx * n, Ly * n, Lz * n, polynomialRestrictionDegeneration_power L n⟩

theorem restrict_right {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U)
    (A : X'' → X' → ℂ) (B : Y'' → Y' → ℂ) (C : Z'' → Z' → ℂ) :
    Deg T (Tensor.restrict A B C U) :=
  h.trans (of_restrict U A B C)

theorem restrict_left {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (A : X'' → X → ℂ) (B : Y'' → Y → ℂ) (C : Z'' → Z → ℂ)
    (h : Deg (Tensor.restrict A B C T) U) : Deg T U :=
  (of_restrict T A B C).trans h

end Deg

end Primal

end

end OAI
