import LPa_Decode
import LPa_StageLaws
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
set_option autoImplicit false
namespace LPa.Decode

theorem values_length (payload : List U8) (start n : Nat) :
    (values payload start n).length = n := LPa.build_length _ _

theorem first_error_bound (payload : List U8) (start n i : Nat)
    (hit : LPa.firstBad (fun j => !((values payload start n)[j]?.getD (true,qzero)).1) n = some i) :
    i < n := LPa.firstBad_bound _ _ _ hit

theorem accepted_values (payload : List U8) (start n : Nat)
    (accepted : LPa.firstBad (fun j => !((values payload start n)[j]?.getD (true,qzero)).1) n = none) :
    ∀ i, i < n → ((values payload start n)[i]?.getD (true,qzero)).1 = true := by
  have all := (LPa.firstBad_none _ _).mp accepted
  intro i bound
  have h := all i bound
  cases hv : ((values payload start n)[i]?.getD (true,qzero)).1 <;> simp_all

#print axioms values_length
#print axioms first_error_bound
#print axioms accepted_values
end LPa.Decode
