inductive Tree where
  | node : List Tree → Tree
theorem t : ∃ x : Tree, x = x := ⟨.node [], rfl⟩
