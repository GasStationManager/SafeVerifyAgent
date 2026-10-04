mutual
inductive Ev : Nat → Prop
  | zero : Ev 0
  | succ : Od n → Ev (n + 1)
inductive Od : Nat → Prop
  | succ : Ev n → Od (n + 1)
end
theorem t : Ev 2 := .succ (.succ .zero)
