import NGW_ConstructorArrays
set_option autoImplicit false
namespace NGW_ArrayLens
open Aeneas Aeneas.Std Result NGW_ConstructorArrays

theorem mutable {α : Type} {n : Usize} (a : Array α n) (i : Usize) (h : i.val<n.val) :
 Array.index_mut_usize a i=ok (NGM_GuardExact.pick a i.val h,fun v=>put a i.val v) := by
 unfold Array.index_mut_usize
 rw [NGM_GuardExact.index a i h]
 rfl

#print axioms mutable
end NGW_ArrayLens
