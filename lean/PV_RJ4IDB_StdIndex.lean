import PV_RJ4IDB_PowersSafety
/-! Semantic boundary for deployed1.94.1 array IndexMut -> slice IndexMut ->
SliceIndex<usize>'s intrinsic index. The native body/forwarding source is
pinned in op254-source-binding.json; compiler intrinsics remain V370. -/
set_option autoImplicit false
namespace R1Z.PV_RJ4IDB_StdIndex
open Aeneas Aeneas.Std Result
variable {A : Type}
/-- Same bounds check, same element, same writeback at the original index. -/
def indexMut {N : Usize} (a : Array A N) (i : Usize) :
 Result (A × (A → Array A N)) :=
 if h : i.val<N.val then
  .ok (a.val[i.val]'(by rw [a.property]; exact h),Aeneas.Std.Array.set a i)
 else .fail .panic

theorem source_equal {N : Usize} (a : Array A N) (i : Usize) :
 indexMut a i = Array.index_mut_usize a i := by
 unfold indexMut Array.index_mut_usize Array.index_usize
 rw [Array.getElem?_Usize_eq]
 by_cases hi : i.val<N.val
 · rw [dif_pos hi,List.getElem?_eq_getElem (by rw [a.property];exact hi)]
   rfl
 · rw [dif_neg hi,List.getElem?_eq_none (by rw [a.property];omega)]
   rfl

theorem in_bounds {N : Usize} (a : Array A N) (i : Usize) (hi : i.val<N.val) :
 ∃ old, indexMut a i = ok (old,Aeneas.Std.Array.set a i) := by
 unfold indexMut
 rw [dif_pos hi]
 exact ⟨_,rfl⟩

theorem out_of_bounds {N : Usize} (a : Array A N) (i : Usize) (hi : N.val ≤ i.val) :
 indexMut a i = fail .panic := by
 unfold indexMut
 rw [dif_neg (by omega)]
#print axioms source_equal
#print axioms in_bounds
#print axioms out_of_bounds
end R1Z.PV_RJ4IDB_StdIndex
