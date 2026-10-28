import PV_B3_CanonicalCAdd
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_cdouble (x : aspis_core.field.CM31) (hx : C x) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.CM31.double x = .ok z ∧ C z :=
  current_cadd x x hx hx
#print axioms current_cdouble
end PV_B3_Canonical
