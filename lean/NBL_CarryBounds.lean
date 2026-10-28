import NBL_AddNative
set_option autoImplicit false
namespace AspisR1.NBL_CarryBounds
open Aeneas Aeneas.Std
open ExtractedIndexedAddSmallNatModelV1

theorem nonempty {xs ys : List Nat} {carry final : Nat}
    (tr : NBA_AddCarry.Trace xs carry ys final) (present : xs≠[]) : final≤1 := by
  induction tr with
  | nil carry => exact False.elim (present rfl)
  | cons digit carry out next final xs ys hd hc frame tail ih =>
    cases xs with
    | nil =>
      cases tail
      exact (NBA_AddCarry.step hd hc frame).2.2.2
    | cons head rest => exact ih (by intro h;cases h)

/-- Native add_small_base_p's final debug bound is established on EVERY
8-digit call, including both passes of gamma and every ordinary input. -/
theorem source (digits out : Digits) (carry last : U32)
    (tr : NBA_AddCarry.Trace (values digits) carry.val (values out) last.val) : last.val≤1 := by
  apply nonempty tr
  intro empty
  have size : (values digits).length=8 := by rw [values,List.length_map];exact digits.property
  rw [empty] at size
  cases size

#print axioms nonempty
#print axioms source
end AspisR1.NBL_CarryBounds
