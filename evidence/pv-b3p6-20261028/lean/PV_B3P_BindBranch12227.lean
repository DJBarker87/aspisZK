import PV_B3P_Ordered227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem bind_branch12 {α β : Type} (p : Prop) [Decidable p]
    (yes no : Result α) (finish : α → Result β) :
    ((if p then yes else no) >>= finish) =
      (if p then yes >>= finish else no >>= finish) := by
  by_cases h : p
  · rw [if_pos h,if_pos h]
  · rw [if_neg h,if_neg h]

theorem bind_return12 {α : Type} (r : Result α) : (r >>= Result.ok) = r := by
  cases r <;> rfl

#print axioms bind_branch12
#print axioms bind_return12
end PV_B3P_Binding12227
