import LPb_ByteFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace LPb_ListWidths
theorem flatMap_length {α β : Type} (f : α → List β) (width : Nat)
    (h : ∀ a, (f a).length = width) (xs : List α) :
    (xs.flatMap f).length = width * xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,Nat.mul_succ]
    omega

theorem array_bytes (n : Usize) (xs : List (Array U8 n)) :
    (xs.flatMap Subtype.val).length = n.val * xs.length :=
  flatMap_length Subtype.val n.val (fun x => x.property) xs
#print axioms flatMap_length
#print axioms array_bytes
end LPb_ListWidths
