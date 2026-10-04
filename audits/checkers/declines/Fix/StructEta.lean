structure P where (a : Nat) (b : Nat)
theorem t (p : P) : p = ⟨p.a, p.b⟩ := rfl
