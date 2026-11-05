import NHX_HighDomain
import NHI_ArrayCells
set_option autoImplicit false
namespace NHX_ArraySlots
open Aeneas Aeneas.Std Result

theorem set_put {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T) :
 Aeneas.Std.Array.set a i x=NHI_ArrayCells.put a i x := by rfl

/-- Exact mutable-slot continuation, including the SAME array backing value. -/
theorem mutable_slot {T : Type} {n : Usize} (a : Array T n) (i : Usize) (bound : i.val<n.val) :
 Array.index_mut_usize a i=ok (NHI_ScalarDomain.pick a i.val bound,
  fun x=>NHI_ArrayCells.put a i x) := by
 simp only [Array.index_mut_usize,NHI_ScalarDomain.index a i bound,bind_tc_ok]
 rfl

#print axioms set_put
#print axioms mutable_slot
end NHX_ArraySlots
