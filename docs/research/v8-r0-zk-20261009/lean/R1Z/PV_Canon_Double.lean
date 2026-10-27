import R1Z.PV_Canon_Add
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
theorem current_double (x : U32) (hx : M x) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.M31.double x = .ok z ∧ M z :=
  current_add x x hx hx
#print axioms current_double
end R1Z.PV_Canon
