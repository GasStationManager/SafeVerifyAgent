import GapCVP

/-! Positive control for the NP-hardness statements: `GapCVP.IsNP` is inhabited.
A verifier machine that accepts every (input, certificate) pair, built against Mathlib's
`FinTM2`, giving `IsNP (fun _ => true) = true`. If this file elaborates, the hypothesis of
every `IsNPHardPromise` theorem is satisfiable, so the theorems are not vacuous in the
degenerate sense. The artifact itself never exhibits such a value. -/

open Turing StateTransition

namespace NPControl

def Γ : Bool → Type
  | false => Bool ⊕ Bool
  | true => Bool

instance instFintypeΓ : ∀ k, Fintype (Γ k)
  | false => inferInstanceAs (Fintype (Bool ⊕ Bool))
  | true => inferInstanceAs (Fintype Bool)

instance instInhabitedΓ : ∀ k, Inhabited (Γ k)
  | false => inferInstanceAs (Inhabited (Bool ⊕ Bool))
  | true => inferInstanceAs (Inhabited Bool)

/-- Pop the input stack until it is empty, then push `true` on the output stack and halt. -/
def main : TM2.Stmt Γ Unit Bool :=
  TM2.Stmt.pop false (fun _ o => o.isSome)
    (TM2.Stmt.branch id (TM2.Stmt.goto fun _ => ())
      (TM2.Stmt.push true (fun _ => true) TM2.Stmt.halt))

def tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Γ
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := fun _ => main

/-- The running configuration: label `()`, state `v`, input stack `l`, output stack empty. -/
def cfg (l : List (Bool ⊕ Bool)) (v : Bool) : tm.Cfg :=
  ⟨some (), v, fun k => match k with | false => l | true => []⟩

/-- The halting configuration the verifier must reach. -/
def halted : tm.Cfg :=
  ⟨none, false, fun k => match k with | false => [] | true => [true]⟩

theorem step_cons (a : Bool ⊕ Bool) (l : List (Bool ⊕ Bool)) (v : Bool) :
    tm.step (cfg (a :: l) v) = some (cfg l true) := by
  refine congrArg (fun S => some (⟨some (), true, S⟩ : tm.Cfg)) ?_
  funext k
  cases k <;> rfl

theorem step_nil (v : Bool) : tm.step (cfg [] v) = some halted := by
  refine congrArg (fun S => some (⟨none, false, S⟩ : tm.Cfg)) ?_
  funext k
  cases k <;> rfl

theorem initList_eq (l : List (Bool ⊕ Bool)) : initList tm l = cfg l false := by
  refine congrArg (fun S => (⟨some (), false, S⟩ : tm.Cfg)) ?_
  funext k
  cases k <;> rfl

theorem haltList_eq : haltList tm [true] = halted := by
  refine congrArg (fun S => (⟨none, false, S⟩ : tm.Cfg)) ?_
  funext k
  cases k <;> rfl

theorem run (l : List (Bool ⊕ Bool)) : ∀ v : Bool, ∃ v' : Bool,
    (flip bind tm.step)^[l.length] (some (cfg l v)) = some (cfg [] v') := by
  induction l with
  | nil => intro v; exact ⟨v, rfl⟩
  | cons a l ih =>
    intro v
    obtain ⟨v', h⟩ := ih true
    refine ⟨v', ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply]
    show (flip bind tm.step)^[l.length] (tm.step (cfg (a :: l) v)) = _
    rw [step_cons]
    exact h

theorem outputs (l : List (Bool ⊕ Bool)) :
    (flip bind tm.step)^[l.length + 1] (some (initList tm l)) = some (haltList tm [true]) := by
  obtain ⟨v', h⟩ := run l false
  rw [initList_eq, haltList_eq, Function.iterate_succ_apply', h]
  exact step_nil v'

/-- The accepting verifier, as the structure `GapCVP.VerifierTM` demands. -/
noncomputable def verifierTM : GapCVP.VerifierTM (fun _ => true) where
  tm := tm
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun := fun a => by
    refine ⟨⟨(GapCVP.pairBitEncoding a).length + 1, ?_⟩, ?_⟩
    · show (flip bind tm.step)^[_ + 1] (some (initList tm (List.map id (GapCVP.pairBitEncoding a))))
        = some (haltList tm (List.map id [true]))
      rw [List.map_id, List.map_id]
      exact outputs _
    · simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

theorem isNP_true : GapCVP.IsNP (fun _ => true) = true := by
  unfold GapCVP.IsNP
  exact @decide_eq_true _ (Classical.propDecidable _) ⟨0, fun _ => true, ⟨verifierTM⟩,
    fun input => ⟨fun _ => ⟨[], by simp, rfl⟩, fun _ => rfl⟩⟩

end NPControl

#print axioms NPControl.isNP_true
