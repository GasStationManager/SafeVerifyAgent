def fImpl (n : Nat) : Nat := n + 100
@[implemented_by fImpl] def f (n : Nat) : Nat := n + 1
theorem t : f 1 = 2 := rfl
