import RPv_FJv_GlobalOwners
import RPv_FJt_GlobalTerminal
import RPu_FJu_GlobalOwners
import RPv_FJs_GlobalPair
import RPu_FIr_GlobalOwners2
import RPu_FJu_Remaining
import RPz8_F3V_Checkpoint
import RPu_FJp_Remaining
import RPz8_FGl_PreparedAt
import RPz7_SAG_NativeFull
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJv_GlobalTerminal
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem owners {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    FJv_GlobalOwners.Owners (FJt_GlobalTerminal.configuration missing err r) B := by
  intro s H e i p q data t prepared calls shape x
  exact FJt_GlobalTerminal.value missing err r B s H e i p q data prepared
#print axioms owners
end AspisR1.FJv_GlobalTerminal
end
