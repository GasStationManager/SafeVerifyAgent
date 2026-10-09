import Audit.Primal.Deg
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Scalar
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexPairingMatrixTensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization

set_option linter.unusedSectionVars false

/-!
# Degree-tracked degeneration on tensor classes (audit, not part of the artifact)

The artifact's `TensorSemiring.TensorClass` is the commutative semiring of finite complex
tensors modulo mutual restriction, ordered by restriction. `DegClass c d` says some
representatives are related by a polynomial restriction degeneration. All the index-type
bookkeeping of the primal construction disappears at this level: the construction becomes an
identity in a commutative semiring.
-/

namespace OAI

open MatrixMultiplication.Foundation
open MatrixMultiplication.AuxiliarySeparation
open MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section

namespace Primal

variable {X Y Z X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Degree-tracked degeneration between classes. -/
def DegClass (c d : TensorClass) : Prop :=
  ∃ T U : FiniteTensor, tensorClass T = c ∧ tensorClass U = d ∧ Deg T.coeff U.coeff

/-- Degree-tracked approximation of a class with rank at most `ρ`. -/
def ApproxClass (c : TensorClass) (ρ : ℕ) : Prop :=
  ∃ T : FiniteTensor, tensorClass T = c ∧ Approx T.coeff ρ

/-! ### Basic closure properties -/

/-- The standard presentation of a tensor degenerates to the tensor itself. -/
private theorem deg_ofTensor_coeff (T : Tensor ℂ X Y Z) :
    Deg (FiniteTensor.ofTensor T).coeff T := by
  have heq : Tensor.pullback (Fintype.equivFin X) (Fintype.equivFin Y) (Fintype.equivFin Z)
      (FiniteTensor.ofTensor T).coeff = T := by
    funext x y z
    simp [FiniteTensor.ofTensor, Tensor.pullback]
  exact (Deg.of_pullback _ _ _ _).trans (Deg.of_eq heq)

theorem DegClass.of_deg {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U) :
    DegClass (classOf T) (classOf U) := by
  exact ⟨FiniteTensor.ofTensor T, FiniteTensor.ofTensor U, rfl, rfl,
    (deg_ofTensor_coeff T).trans (h.trans (Deg.of_pullback U _ _ _))⟩

/-- Every class has a finite-tensor representative. -/
private theorem exists_tensorClass_eq (c : TensorClass) :
    ∃ T : FiniteTensor, tensorClass T = c := by
  induction c using Quotient.inductionOn with
  | h T => exact ⟨T, rfl⟩

theorem DegClass.refl (c : TensorClass) : DegClass c c := by
  obtain ⟨T, rfl⟩ := exists_tensorClass_eq c
  exact ⟨T, T, rfl, rfl, Deg.refl T.coeff⟩

/-- A restriction is a degeneration: `d ≤ c` gives `DegClass c d`. -/
theorem DegClass.of_le {c d : TensorClass} (h : d ≤ c) : DegClass c d := by
  obtain ⟨T, rfl⟩ := exists_tensorClass_eq c
  obtain ⟨U, rfl⟩ := exists_tensorClass_eq d
  obtain ⟨A, B, C, hU⟩ := (tensorClass_le_iff U T).mp h
  refine ⟨T, U, rfl, rfl, ?_⟩
  rw [hU]
  exact Deg.of_restrict T.coeff A B C

theorem DegClass.trans {c d e : TensorClass} (h₁ : DegClass c d) (h₂ : DegClass d e) :
    DegClass c e := by
  obtain ⟨T, U, hT, hU, hTU⟩ := h₁
  obtain ⟨U', V, hU', hV, hU'V⟩ := h₂
  obtain ⟨A, B, C, hA⟩ := ((tensorClass_eq_iff U' U).mp (hU'.trans hU.symm)).1
  have hUU' : Deg U.coeff U'.coeff := by
    rw [hA]
    exact Deg.of_restrict U.coeff A B C
  exact ⟨T, V, hT, hV, (hTU.trans hUU').trans hU'V⟩

theorem DegClass.mono_left {c c' d : TensorClass} (h : DegClass c d) (hc : c ≤ c') :
    DegClass c' d :=
  (DegClass.of_le hc).trans h

theorem DegClass.mono_right {c d d' : TensorClass} (h : DegClass c d) (hd : d' ≤ d) :
    DegClass c d' :=
  h.trans (DegClass.of_le hd)

theorem DegClass.mul {c c' d d' : TensorClass} (h : DegClass c d) (h' : DegClass c' d') :
    DegClass (c * c') (d * d') := by
  obtain ⟨T, U, rfl, rfl, hTU⟩ := h
  obtain ⟨T', U', rfl, rfl, hTU'⟩ := h'
  rw [tensorClass_product, tensorClass_product]
  exact DegClass.of_deg (Deg.product hTU hTU')

theorem DegClass.pow {c d : TensorClass} (h : DegClass c d) (n : ℕ) :
    DegClass (c ^ n) (d ^ n) := by
  induction n with
  | zero => simpa using DegClass.refl 1
  | succ n ih => simpa [pow_succ] using ih.mul h

theorem ApproxClass.of_rank (c : TensorClass) : ApproxClass c (rank c) := by
  obtain ⟨T, rfl⟩ := exists_tensorClass_eq c
  refine ⟨T, rfl, ?_⟩
  rw [rank_tensorClass]
  exact Approx.of_rankAtMost (exactRank_spec T.coeff)

theorem ApproxClass.mono {c : TensorClass} {ρ ρ' : ℕ} (h : ApproxClass c ρ) (hρ : ρ ≤ ρ') :
    ApproxClass c ρ' := by
  obtain ⟨T, hT, hA⟩ := h
  exact ⟨T, hT, hA.mono hρ⟩

theorem ApproxClass.of_degClass {c d : TensorClass} {ρ : ℕ} (h : DegClass c d)
    (hc : ApproxClass c ρ) : ApproxClass d ρ := by
  obtain ⟨T, U, hT, hU, hTU⟩ := h
  obtain ⟨T', hT', hA⟩ := hc
  obtain ⟨A, B, C, hTA⟩ := ((tensorClass_eq_iff T T').mp (hT.trans hT'.symm)).1
  refine ⟨U, hU, hTU.toApprox ?_⟩
  rw [hTA]
  exact hA.restrict A B C

theorem classOf_power (T : Tensor ℂ X Y Z) (n : ℕ) :
    classOf (Tensor.power T n) = classOf T ^ n := by
  induction n with
  | zero =>
    have hzero : Tensor.power T 0 = Tensor.pullback
        (Equiv.equivPUnit (Fin 0 → X) : (Fin 0 → X) ≃ PUnit.{1})
        (Equiv.equivPUnit (Fin 0 → Y) : (Fin 0 → Y) ≃ PUnit.{1})
        (Equiv.equivPUnit (Fin 0 → Z) : (Fin 0 → Z) ≃ PUnit.{1})
        (fun (_ _ _ : PUnit.{1}) => (1 : ℂ)) := by
      funext x y z
      simp [Tensor.power, Tensor.pullback]
    rw [hzero, classOf_reindex, pow_zero]
    rfl
  | succ n ih =>
    have heq : Tensor.power T (n + 1) = Tensor.pullback
        (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
        (Tensor.product T (Tensor.power T n)) := by
      funext x y z
      simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
        Fin.prod_univ_succ, Fin.tail]
    rw [heq, classOf_reindex, classOf_product, ih, pow_succ']

/-- Bini's interpolation at class level: an approximation of rank `ρ` bounds the rank of every
power with linear overhead. -/
theorem ApproxClass.rank_pow {c : TensorClass} {ρ : ℕ} (h : ApproxClass c ρ) :
    ∃ D : ℕ, ∀ m : ℕ, rank (c ^ m) ≤ (D * m + 1) * ρ ^ m := by
  obtain ⟨T, rfl, hA⟩ := h
  obtain ⟨D, hD⟩ := hA.rank_power
  refine ⟨D, fun m => ?_⟩
  rw [← classOf_coeff, ← classOf_power, rank_classOf]
  exact exactRank_le (hD m)

/-! ### The six leg permutations -/

/-- The product of the classes of the six leg permutations of `T`. -/
def sym6class (T : Tensor ℂ X Y Z) : TensorClass :=
  classOf T * classOf (Tensor.cyclic T) * classOf (Tensor.cyclic (Tensor.cyclic T)) *
    classOf (swapYZ T) * classOf (Tensor.cyclic (swapYZ T)) *
    classOf (Tensor.cyclic (Tensor.cyclic (swapYZ T)))

/-- `S a b` is the paper's six-fold symmetrised polynomial multiplication, as a class. -/
def S (a b : ℕ) : TensorClass := sym6class (convolution a b)

/-- The first-leg dot product `B_X(m)` as a class. -/
def dotX (m : ℕ) : TensorClass :=
  classOf (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m))))

theorem sym6class_cyclic (T : Tensor ℂ X Y Z) :
    sym6class (Tensor.cyclic T) = sym6class T := by
  unfold sym6class
  show classOf (Tensor.cyclic T) * classOf (Tensor.cyclic (Tensor.cyclic T)) * classOf T *
      classOf (Tensor.cyclic (Tensor.cyclic (swapYZ T))) * classOf (swapYZ T) *
      classOf (Tensor.cyclic (swapYZ T)) = _
  ring

theorem sym6class_swapYZ (T : Tensor ℂ X Y Z) :
    sym6class (swapYZ T) = sym6class T := by
  unfold sym6class
  show classOf (swapYZ T) * classOf (Tensor.cyclic (swapYZ T)) *
      classOf (Tensor.cyclic (Tensor.cyclic (swapYZ T))) * classOf T *
      classOf (Tensor.cyclic T) * classOf (Tensor.cyclic (Tensor.cyclic T)) = _
  ring

theorem sym6class_reindex (T : Tensor ℂ X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    sym6class (Tensor.pullback ex ey ez T) = sym6class T := by
  unfold sym6class
  show classOf (Tensor.pullback ex ey ez T) *
      classOf (Tensor.pullback ey ez ex (Tensor.cyclic T)) *
      classOf (Tensor.pullback ez ex ey (Tensor.cyclic (Tensor.cyclic T))) *
      classOf (Tensor.pullback ex ez ey (swapYZ T)) *
      classOf (Tensor.pullback ez ey ex (Tensor.cyclic (swapYZ T))) *
      classOf (Tensor.pullback ey ex ez (Tensor.cyclic (Tensor.cyclic (swapYZ T)))) = _
  simp only [classOf_reindex]

theorem sym6class_product (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') :
    sym6class (Tensor.product T U) = sym6class T * sym6class U := by
  unfold sym6class
  show classOf (Tensor.product T U) *
      classOf (Tensor.product (Tensor.cyclic T) (Tensor.cyclic U)) *
      classOf (Tensor.product (Tensor.cyclic (Tensor.cyclic T))
        (Tensor.cyclic (Tensor.cyclic U))) *
      classOf (Tensor.product (swapYZ T) (swapYZ U)) *
      classOf (Tensor.product (Tensor.cyclic (swapYZ T)) (Tensor.cyclic (swapYZ U))) *
      classOf (Tensor.product (Tensor.cyclic (Tensor.cyclic (swapYZ T)))
        (Tensor.cyclic (Tensor.cyclic (swapYZ U)))) = _
  simp only [classOf_product]
  ring

theorem sym6class_power (T : Tensor ℂ X Y Z) (n : ℕ) :
    sym6class (Tensor.power T n) = sym6class T ^ n := by
  unfold sym6class
  show classOf (Tensor.power T n) * classOf (Tensor.power (Tensor.cyclic T) n) *
      classOf (Tensor.power (Tensor.cyclic (Tensor.cyclic T)) n) *
      classOf (Tensor.power (swapYZ T) n) *
      classOf (Tensor.power (Tensor.cyclic (swapYZ T)) n) *
      classOf (Tensor.power (Tensor.cyclic (Tensor.cyclic (swapYZ T))) n) = _
  simp only [classOf_power]
  ring

/-- The six permutations of a dot product multiply to two matrix multiplications. -/
theorem sym6class_dot (m : ℕ) :
    sym6class (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m)))) =
      matrixClass m ^ 2 := by
  have hsym : swapYZ (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m)))) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m))) := by
    funext u j i
    simp only [swapYZ, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have htriple : classOf (Tensor.dotPairing (K := ℂ) (Fin m)) *
      classOf (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m))) *
      classOf (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m)))) =
      matrixClass m := by
    rw [← classOf_product, ← classOf_product]
    change classOf (Tensor.pairingTriple (K := ℂ) (Fin m) (Fin m) (Fin m)) =
      classOf (Tensor.matrixCoefficients (K := ℂ) (Fin m) (Fin m) (Fin m))
    exact (classOf_eq_of_reindex _ _ _ Tensor.pairingTriple_matrixCoefficients).symm
  unfold sym6class
  rw [hsym]
  show classOf (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m)))) *
      classOf (Tensor.dotPairing (K := ℂ) (Fin m)) *
      classOf (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m))) *
      classOf (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m)))) *
      classOf (Tensor.dotPairing (K := ℂ) (Fin m)) *
      classOf (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m))) = _
  rw [← htriple]
  ring

/-- `C(1,b) ≅ B_X(b)`, so `S 1 b = T_b ⊗ T_b`. -/
theorem S_one (b : ℕ) : S 1 b = matrixClass b ^ 2 := by
  unfold S
  rw [← sym6class_reindex (convolution 1 b) convolutionOneInputEquiv (Equiv.refl (Fin b))
    (convolutionOneOutputEquiv b), convolution_one_left_dotPairing, sym6class_dot]

theorem S_comm (a b : ℕ) : S a b = S b a := by
  have h : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a))
      (finCongr (by omega : b + a - 1 = a + b - 1))
      (swapYZ (Tensor.cyclic (convolution a b))) = convolution b a := by
    funext i j k
    simp [Tensor.pullback, swapYZ, Tensor.cyclic, convolution, Nat.add_comm]
  unfold S
  rw [← h, sym6class_reindex, sym6class_swapYZ, sym6class_cyclic]

private theorem exactRank_cyclic_le {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor ℂ A B C) : exactRank (Tensor.cyclic T) ≤ exactRank T :=
  exactRank_le (exactRank_spec T).cyclic

private theorem exactRank_swapYZ_le {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor ℂ A B C) : exactRank (swapYZ T) ≤ exactRank T :=
  exactRank_le (T := swapYZ T) (exactRank_spec T).cyclic.swapXY.cyclic.cyclic

private theorem rank_sym6class_le_aux (T : Tensor ℂ X Y Z) :
    rank (sym6class T) ≤ exactRank T ^ 6 := by
  have key : ∀ (p q : TensorClass) (r s : ℕ), rank p ≤ r → rank q ≤ s → rank (p * q) ≤ r * s :=
    fun p q r s hp hq => (rank_mul_le p q).trans (Nat.mul_le_mul hp hq)
  have e0 : rank (classOf T) ≤ exactRank T := (rank_classOf T).le
  have e1 : rank (classOf (Tensor.cyclic T)) ≤ exactRank T := by
    rw [rank_classOf]
    exact exactRank_cyclic_le T
  have e2 : rank (classOf (Tensor.cyclic (Tensor.cyclic T))) ≤ exactRank T := by
    rw [rank_classOf]
    exact (exactRank_cyclic_le _).trans (exactRank_cyclic_le T)
  have e3 : rank (classOf (swapYZ T)) ≤ exactRank T := by
    rw [rank_classOf]
    exact exactRank_swapYZ_le T
  have e4 : rank (classOf (Tensor.cyclic (swapYZ T))) ≤ exactRank T := by
    rw [rank_classOf]
    exact (exactRank_cyclic_le _).trans (exactRank_swapYZ_le T)
  have e5 : rank (classOf (Tensor.cyclic (Tensor.cyclic (swapYZ T)))) ≤ exactRank T := by
    rw [rank_classOf]
    exact (exactRank_cyclic_le _).trans ((exactRank_cyclic_le _).trans (exactRank_swapYZ_le T))
  unfold sym6class
  calc _ ≤ exactRank T * exactRank T * exactRank T * exactRank T * exactRank T * exactRank T :=
        key _ _ _ _ (key _ _ _ _ (key _ _ _ _ (key _ _ _ _ (key _ _ _ _ e0 e1) e2) e3) e4) e5
    _ = exactRank T ^ 6 := by ring

theorem rank_S_le (a b : ℕ) : rank (S a b) ≤ (a + b - 1) ^ 6 := by
  exact (rank_sym6class_le_aux (convolution a b)).trans
    (Nat.pow_le_pow_left (exactRank_le (convolution_rankAtMost a b)) 6)

/-- `m` disjoint copies of a tensor form the class `m * classOf T`. -/
theorem classOf_copies (m : ℕ) (T : Tensor ℂ X Y Z) :
    classOf (Tensor.directSum (fun _ : Fin m => T)) = (m : TensorClass) * classOf T := by
  rw [classOf_directSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A cyclic leg permutation of a nonzero tensor is nonzero. -/
private theorem cyclic_ne_zero {T : Tensor ℂ X Y Z} (hT : T ≠ 0) : Tensor.cyclic T ≠ 0 := by
  intro h
  apply hT
  funext x y z
  exact congrFun (congrFun (congrFun h y) z) x

/-- Exchanging the last two legs of a nonzero tensor gives a nonzero tensor. -/
private theorem swapYZ_ne_zero {T : Tensor ℂ X Y Z} (hT : T ≠ 0) : swapYZ T ≠ 0 := by
  intro h
  apply hT
  funext x y z
  exact congrFun (congrFun (congrFun h x) z) y

/-- A nonzero tensor has a nonzero class. -/
private theorem classOf_ne_zero {T : Tensor ℂ X Y Z} (hT : T ≠ 0) : classOf T ≠ 0 :=
  fun h => hT ((classOf_eq_zero_iff T).mp h)

/-- Tensor classes have no zero divisors: both factors dominate `1`. -/
private theorem class_mul_ne_zero {c d : TensorClass} (hc : c ≠ 0) (hd : d ≠ 0) :
    c * d ≠ 0 := by
  intro h
  have h1 : (1 : TensorClass) ≤ c * d := by
    simpa using mul_mono (one_le_of_ne_zero hc) (one_le_of_ne_zero hd)
  rw [h] at h1
  exact one_ne_zero (le_antisymm h1 (zero_le 1))

theorem S_ne_zero (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : S a b ≠ 0 := by
  have h0 : convolution a b ≠ 0 := convolution_nonzero ha hb
  have hs : swapYZ (convolution a b) ≠ 0 := swapYZ_ne_zero h0
  exact class_mul_ne_zero (class_mul_ne_zero (class_mul_ne_zero (class_mul_ne_zero
    (class_mul_ne_zero (classOf_ne_zero h0) (classOf_ne_zero (cyclic_ne_zero h0)))
    (classOf_ne_zero (cyclic_ne_zero (cyclic_ne_zero h0)))) (classOf_ne_zero hs))
    (classOf_ne_zero (cyclic_ne_zero hs))) (classOf_ne_zero (cyclic_ne_zero (cyclic_ne_zero hs)))

/-! ### Restriction order and the six permutations -/

/-- `swapYZ` is a composite of the artifact's `cyclic` and `swapXY` (definitionally). -/
theorem swapYZ_eq (T : Tensor ℂ X Y Z) :
    swapYZ T = Tensor.cyclic (Tensor.cyclic (Tensor.swapXY (Tensor.cyclic T))) := rfl

theorem IsRestriction.cyclic {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : IsRestriction T U) : IsRestriction (Tensor.cyclic T) (Tensor.cyclic U) := by
  obtain ⟨A, B, C, rfl⟩ := h
  exact ⟨B, C, A, Tensor.cyclic_restrict A B C U⟩

private theorem swapYZ_restrict {A' B' C' : Type*} {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (MA : A' → A → ℂ) (MB : B' → B → ℂ) (MC : C' → C → ℂ) (P : Tensor ℂ A B C) :
    swapYZ (Tensor.restrict MA MB MC P) = Tensor.restrict MA MC MB (swapYZ P) := by
  funext x' z' y'
  simp only [swapYZ, Tensor.restrict]
  apply Finset.sum_congr rfl
  intro x _
  refine Finset.sum_comm.trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem IsRestriction.swapYZ {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : IsRestriction T U) : IsRestriction (swapYZ T) (swapYZ U) := by
  obtain ⟨A, B, C, rfl⟩ := h
  exact ⟨A, C, B, swapYZ_restrict A B C U⟩

/-- The symmetrised class is monotone in the restriction order. -/
theorem sym6class_mono {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : classOf T ≤ classOf U) : sym6class T ≤ sym6class U := by
  have h0 : IsRestriction T U := (classOf_le_iff T U).mp h
  have h3 : IsRestriction (swapYZ T) (swapYZ U) := IsRestriction.swapYZ h0
  unfold sym6class
  exact mul_mono (mul_mono (mul_mono (mul_mono (mul_mono h
    ((classOf_le_iff _ _).mpr (IsRestriction.cyclic h0)))
    ((classOf_le_iff _ _).mpr (IsRestriction.cyclic (IsRestriction.cyclic h0))))
    ((classOf_le_iff _ _).mpr h3))
    ((classOf_le_iff _ _).mpr (IsRestriction.cyclic h3)))
    ((classOf_le_iff _ _).mpr (IsRestriction.cyclic (IsRestriction.cyclic h3)))

theorem sym6class_congr {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : classOf T = classOf U) : sym6class T = sym6class U :=
  le_antisymm (sym6class_mono h.le) (sym6class_mono h.ge)

private theorem swapYZ_directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor ℂ X Y Z) :
    swapYZ (Tensor.directSum T) = Tensor.directSum (fun i => swapYZ (T i)) := by
  funext x z y
  rcases x with ⟨i, x⟩
  rcases z with ⟨k, z⟩
  rcases y with ⟨j, y⟩
  simp only [swapYZ, Tensor.directSum, and_comm]

/-- `m` disjoint copies, symmetrised: the multiplicity is charged on all six legs. -/
theorem sym6class_copies (m : ℕ) (T : Tensor ℂ X Y Z) :
    sym6class (Tensor.directSum (fun _ : Fin m => T)) = (m : TensorClass) ^ 6 * sym6class T := by
  unfold sym6class
  simp only [Tensor.cyclic_directSum, swapYZ_directSum, classOf_copies]
  ring

/-- A degeneration of tensors is a degeneration of their symmetrised classes. -/
theorem DegClass.sym6 {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} (h : Deg T U) :
    DegClass (sym6class T) (sym6class U) := by
  unfold sym6class
  exact (((((DegClass.of_deg h).mul (DegClass.of_deg h.cyclic)).mul
    (DegClass.of_deg h.cyclic.cyclic)).mul (DegClass.of_deg h.swapYZ)).mul
    (DegClass.of_deg h.swapYZ.cyclic)).mul (DegClass.of_deg h.swapYZ.cyclic.cyclic)

/-- The rank of a symmetrised class is at most the sixth power of the rank. -/
theorem rank_sym6class_le (T : Tensor ℂ X Y Z) :
    rank (sym6class T) ≤ exactRank T ^ 6 := by
  exact rank_sym6class_le_aux T

end Primal

end

end OAI
