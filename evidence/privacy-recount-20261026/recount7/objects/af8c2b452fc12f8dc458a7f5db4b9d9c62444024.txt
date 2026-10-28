import PV_B3_ZeroArrays
namespace PV_B3_TripleIndexD336
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem index {A : Type} (x : A) (i : Usize) (hi : i.val < 3) :
    Array.index_usize (Array.make 3#usize [x,x,x]) i = ok x := by
  rw [PV_B3_ZeroArrays.triple_repeat]
  exact PV_B3_ZeroArithmetic.index_repeat 3#usize x i hi

#print axioms index
end PV_B3_TripleIndexD336
