import ARX_Root
import FIp_Blockers
import FIr_FinalInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_InstallationBoundary
open Aeneas Aeneas.Std Result DrvC_Installation
/-- The adopted root's selected configuration retains the supplied terminal. -/
theorem adopted {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).boundaries.terminal=c.boundaries.terminal := rfl
/-- The separate FIq installation fixes the actual body used by these proofs. -/
theorem fixed {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIq_Install.configuration err c r).boundaries.terminal=FIq_Terminal.terminal := rfl
/-- Arbitrarily selected returns remain possible at the adopted callback slot.
This is an installation observation, not a forged accepted execution. -/
theorem arbitrary {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (value : FIp_SemanticArithmetic.MQ)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array FIp_SemanticArithmetic.MQ 29#usize) 3#usize)
    (alpha : Array FIp_SemanticArithmetic.MQ 10#usize)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges) :
    let chosen := {c with boundaries:={c.boundaries with terminal:=fun _ _ _ _ => ok (.Ok value)}}
    (FIp_Install.configuration err chosen r).boundaries.terminal pub claims alpha challenges=ok (.Ok value) :=
  FIp_Blockers.arbitrary_terminal err c r value pub claims alpha challenges
#print axioms adopted
#print axioms fixed
#print axioms arbitrary
end AspisR1.FJn_InstallationBoundary
end
