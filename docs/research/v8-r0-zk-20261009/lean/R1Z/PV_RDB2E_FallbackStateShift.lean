import R1Z.PV_RDB2E_FallbackRoundsModel

section
-- Unchanged source component R1Z.PV_CBL_FallbackStateShift
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackStateShift
open PV_CBL_FallbackScalar
set_option autoImplicit false
theorem two_c (s : State) (w0 w1 : U32) : (step (step s w0) w1).c=s.a := rfl
theorem two_d (s : State) (w0 w1 : U32) : (step (step s w0) w1).d=s.b := rfl
theorem two_g (s : State) (w0 w1 : U32) : (step (step s w0) w1).g=s.e := rfl
theorem two_h (s : State) (w0 w1 : U32) : (step (step s w0) w1).h=s.f := rfl
#print axioms two_c
#print axioms two_d
#print axioms two_g
#print axioms two_h
end R1Z.PV_CBL_FallbackStateShift

end
