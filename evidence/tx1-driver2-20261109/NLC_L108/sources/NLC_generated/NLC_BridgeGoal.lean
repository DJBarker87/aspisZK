import NLC_InitializedInvocation
import NKA_FinishTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Goals
open Aeneas Aeneas.Std AspisR1PublicPreparation NLC_Finish
/-- TYPE-CHECKED GOAL ONLY. No proof of this equality is submitted. It is the
exact remaining source bridge before the machine fold can be used for finish. -/
def FinishSourceEquality {H : Type} (input : Input H) : Prop :=
 PreparedHashCode.run (fold (fuel (initial input)) (initial input)) =
 PreparedHashCode.run (S1SemanticCode.finish NJM_RoundJoin.R
   (IDa_Deployed.boundaries input.reservation) input.digest input.publicValue
   input.prefix1 input.transcript input.challenges none)
#check FinishSourceEquality
#print FinishSourceEquality
end AspisR1.NLC_Goals
end
