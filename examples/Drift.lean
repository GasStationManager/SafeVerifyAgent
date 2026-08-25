/-- `Sorted xs` says the list `xs` is sorted in non-decreasing order. -/
def Sorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | x :: y :: r => x ≤ y ∧ Sorted r

/-- `check xs` decides whether `xs` is sorted. -/
def check : List Nat → Bool
  | []          => true
  | [_]         => true
  | x :: y :: r => (x ≤ y) && check r

/-- `check` is sound: if it accepts a list, that list really is sorted. -/
theorem check_sound : ∀ xs, check xs = true → Sorted xs := by
  intro xs
  induction xs using check.induct with
  | case1 => intro _; trivial
  | case2 _ => intro _; trivial
  | case3 x y r ih =>
    intro h
    simp [check] at h
    exact ⟨h.1, ih h.2⟩

#print axioms check_sound
