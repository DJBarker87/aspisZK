import FJv_GlobalOwners
import FJt_GlobalTerminal
import FJu_GlobalOwners
import FJs_GlobalPair
import FIr_GlobalOwners2
import FJu_Remaining
import F3V_Checkpoint
import FJp_Remaining
import FGl_PreparedAt
import SAG_NativeFull
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
