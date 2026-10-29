import R1Z.PV_RunJoin_CircleOwnedCarrier52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedProjection52
open PV_RunJoin_CircleOwnedCarrier52
theorem cm_a (a : CM) : (encCM a).a=a.1 := rfl
theorem cm_b (a : CM) : (encCM a).b=a.2 := rfl
theorem q_c0 (a : Q) : (encQ a).c0=encCM a.1 := rfl
theorem q_c1 (a : Q) : (encQ a).c1=encCM a.2 := rfl

#print axioms cm_a
#print axioms cm_b
#print axioms q_c0
#print axioms q_c1
end R1Z.PV_RunJoin_CircleOwnedProjection52
