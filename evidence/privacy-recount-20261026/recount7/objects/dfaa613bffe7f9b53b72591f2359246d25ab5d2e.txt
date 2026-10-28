import PV_B3_CanonicalAdd
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result
theorem current_double (x : U32) (hx : M x) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.M31.double x = .ok z ∧ M z :=
  current_add x x hx hx
#print axioms current_double
end PV_B3_Canonical
