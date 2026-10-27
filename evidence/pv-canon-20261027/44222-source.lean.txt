import R1Z.PV_Canon_CAdd
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_cdouble (x : aspis_core.field.CM31) (hx : C x) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.CM31.double x = .ok z ∧ C z :=
  current_cadd x x hx hx
#print axioms current_cdouble
end R1Z.PV_Canon
