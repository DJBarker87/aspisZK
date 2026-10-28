import PV_B3P_HelperIndex224
namespace PV_B3P_HelperMut224
open Aeneas Aeneas.Std PV_B3P_HelperIndex224
set_option autoImplicit false

theorem zero {α : Type} (xs : Array α 2#usize) :
    Array.index_mut_usize xs 0#usize = .ok (PV_B3P_HelperIndex224.zero xs,xs.set 0#usize) := by
  rw [Array.index_mut_usize,index_zero]
  rfl

theorem one {α : Type} (xs : Array α 2#usize) :
    Array.index_mut_usize xs 1#usize = .ok (PV_B3P_HelperIndex224.one xs,xs.set 1#usize) := by
  rw [Array.index_mut_usize,index_one]
  rfl

#print axioms zero
#print axioms one
end PV_B3P_HelperMut224
