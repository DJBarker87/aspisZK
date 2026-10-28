import NDD_Reference.Funs
import NDD_ResultLaws
import FIn_WeightsFuns
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_ScalarCanon

theorem checked_add (x y : U32) (bound : x.val+y.val < 2^32) :
    x+y = ok (U32.wrapping_add x y) := by
  scalar_tac

theorem checked_sub (x y : U32) (bound : y.val ≤ x.val) :
    x-y = ok (U32.wrapping_sub x y) := by
  scalar_tac

#print axioms checked_add
#print axioms checked_sub
end NDD_ScalarCanon
