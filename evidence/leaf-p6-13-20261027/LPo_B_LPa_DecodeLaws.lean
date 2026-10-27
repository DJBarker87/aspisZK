import LPo_B_LPa_Decode
import LPo_B_LPa_StageLaws
open Aeneas Aeneas.Std Result
open LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPo.BA.Decode

theorem values_length (payload : List U8) (start n : Nat) :
    (values payload start n).length = n := LPo.BA.build_length _ _

theorem first_error_bound (payload : List U8) (start n i : Nat)
    (hit : LPo.BA.firstBad (fun j => !((values payload start n)[j]?.getD (true,qzero)).1) n = some i) :
    i < n := LPo.BA.firstBad_bound _ _ _ hit

theorem accepted_values (payload : List U8) (start n : Nat)
    (accepted : LPo.BA.firstBad (fun j => !((values payload start n)[j]?.getD (true,qzero)).1) n = none) :
    ∀ i, i < n → ((values payload start n)[i]?.getD (true,qzero)).1 = true := by
  have all := (LPo.BA.firstBad_none _ _).mp accepted
  intro i bound
  have h := all i bound
  cases hv : ((values payload start n)[i]?.getD (true,qzero)).1 <;> simp_all

#print axioms values_length
#print axioms first_error_bound
#print axioms accepted_values
end LPo.BA.Decode
