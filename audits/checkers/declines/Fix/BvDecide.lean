import Std.Tactic.BVDecide
theorem t (x : BitVec 8) : x &&& x = x := by bv_decide
