import Hiq_ReleaseRoute
set_option autoImplicit false
namespace AspisR1.Hiq_RouteHead
open Aeneas Aeneas.Std

theorem head_take {A : Type} (xs : List A) (n : Nat) : (xs.take (n+1)).head? = xs.head? := by
  cases xs <;> rfl

theorem first_head (data : Slice U8) (h : Hiq_ReleaseRoute.stage1 data) : data.val.head? = some 3#u8 := by
  rcases h with h | h <;> rw [h] <;> rfl

theorem second_head (data : Slice U8) (h : Hiq_ReleaseRoute.asq8 data) : data.val.head? = some 65#u8 := by
  have hh := congrArg List.head? h
  exact (head_take data.val 3).symm.trans hh

theorem reject_other (data : Slice U8) (tag : U8) (head : data.val.head? = some tag)
    (not3 : tag ≠ 3#u8) (not65 : tag ≠ 65#u8) : Hiq_ReleaseRoute.route data = .reject := by
  apply Hiq_ReleaseRoute.reject_iff.mpr
  constructor
  · intro h
    exact not3 (Option.some.inj (head.symm.trans (first_head data h)))
  · intro h
    exact not65 (Option.some.inj (head.symm.trans (second_head data h)))

#print axioms head_take
#print axioms first_head
#print axioms second_head
#print axioms reject_other
end AspisR1.Hiq_RouteHead
