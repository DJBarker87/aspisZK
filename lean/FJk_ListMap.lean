import Mathlib.Algebra.Ring.Hom.Defs
set_option autoImplicit false
namespace AspisR1.FJk_ListMap
variable {K L : Type} [NonAssocSemiring K] [NonAssocSemiring L]
/-- The default zero is transported even beyond the end of a family list. -/
theorem getD (g : K →+* L) (xs : List K) (i : Nat) :
    g (xs.getD i 0)=(xs.map g).getD i 0 := by
  induction xs generalizing i with
  | nil => simp only [List.map_nil,List.getD_nil,map_zero]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i
#print axioms getD
end AspisR1.FJk_ListMap
