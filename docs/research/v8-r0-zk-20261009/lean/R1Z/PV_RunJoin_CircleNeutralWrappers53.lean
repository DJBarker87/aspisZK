import R1Z.PV_RunJoin_CircleNeutralWord53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralWrappers53
theorem add32 (a b : U32) : core.num.U32.wrapping_add a b = U32.wrapping_add a b := rfl
theorem sub32 (a b : U32) : core.num.U32.wrapping_sub a b = U32.wrapping_sub a b := rfl
theorem add64 (a b : U64) : core.num.U64.wrapping_add a b = U64.wrapping_add a b := rfl
theorem sub64 (a b : U64) : core.num.U64.wrapping_sub a b = U64.wrapping_sub a b := rfl
theorem mul64 (a b : U64) : core.num.U64.wrapping_mul a b = U64.wrapping_mul a b := rfl

#print axioms add32
#print axioms sub32
#print axioms add64
#print axioms sub64
#print axioms mul64
end R1Z.PV_RunJoin_CircleNeutralWrappers53
