import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_Blockers
open Aeneas Aeneas.Std Result DrvC_Installation

theorem dots_fixed {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).query.op20=FIp_DotsAdapter.dots := rfl

theorem arbitrary_terminal {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (value : FIp_SemanticArithmetic.MQ)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array FIp_SemanticArithmetic.MQ 29#usize) 3#usize)
    (alpha : Array FIp_SemanticArithmetic.MQ 10#usize)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges) :
    let chosen := {c with boundaries:={c.boundaries with terminal:=fun _ _ _ _ => ok (.Ok value)}}
    (FIp_Install.configuration err chosen r).boundaries.terminal pub claims alpha challenges=ok (.Ok value) := rfl

#print axioms dots_fixed
#print axioms arbitrary_terminal
end AspisR1.FIp_Blockers
end
