import R1Z.PV_RunJoin_InstalledFamily
import R1Z.PV_RunJoin_InstalledTransport
import R1Z.PV_RunJoin_PublicCarrierFrame
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceSelectionContract
open R0P R0Z R0Z.FsStatement R0Z.JointView R1Z.GamesR1
local notation "K" => PrivacyR1AcctBasis.K
variable {CommitHandle : Type}

/-- Exact installed inputs/transport consumed by source identification. The
actual selection, compiler success and RspendPlus proof remain to be installed.
No proof field below is an axiom or an inferred source theorem. -/
structure Data where
  selection : PV_RunJoin_InstalledFamily.Selection CommitHandle
  publicBinding : PV_RunJoin_InstalledFamily.PublicBinding selection

abbrev endpointHonest := PhaseWireLog2Bin.honest PV_RunJoin_SourceEndpoint.input

theorem installed_row (j : Fin 1024) : endpointHonest.transport j = PV_Src_Transport.row j :=
  PV_RunJoin_InstalledTransport.endpoint_row_call j

/-- Expose the SAME selected compilation rather than accepting another output
with a convenient public statement. Native successful-run/admission laws must
refer to this exact record. -/
def selectedRecord (d : Data (CommitHandle := CommitHandle))
    (x : Statement K CommitHandle) (w : endpointHonest.Instance) :=
  d.selection.selected endpointHonest x w

theorem selected_public (d : Data (CommitHandle := CommitHandle))
    (x : Statement K CommitHandle) (w : endpointHonest.Instance)
    (hw : endpointHonest.public w = x.1) :
    PV_Src_NativeInput.publicInput (selectedRecord d x w) =
      PV_Src_NativeInput.publicInput (d.selection.publicRecord x) :=
  d.publicBinding endpointHonest x w hw

#print Data
#print selectedRecord
#print axioms installed_row
#print axioms selected_public
end R1Z.PV_RunJoin_SourceSelectionContract
