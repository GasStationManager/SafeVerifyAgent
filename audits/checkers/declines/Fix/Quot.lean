def R (a b : Nat) : Prop := True
theorem t : Quot.mk R 1 = Quot.mk R 2 := Quot.sound trivial
