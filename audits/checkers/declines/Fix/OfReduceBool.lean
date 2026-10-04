def b : Bool := decide (2 ^ 20 % 7 = 4)
theorem t : b = true := Lean.ofReduceBool b true (by rfl)
