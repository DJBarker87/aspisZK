import F3K_CheckpointPreparedFields
import F3L_RhoMeaning
import CheckpointBytes5Output
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SourceNumeric
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem wide (x : AspisR1PublicPreparation.aspis_core.field.WideExact) :
    CheckpointBytes5Output.ofE (Tx1Q_Carriers.e (currentE x))=decode (toClaimE x) := by
  rfl

theorem qm (x : AspisR1PublicPreparation.aspis_core.field.QM31) :
    CheckpointBytes5Output.ofK (Tx1Q_Carriers.k (currentQ x))=F3L_RhoMeaning.decode x := by
  rfl

#print axioms wide
#print axioms qm
end AspisR1.F3L_SourceNumeric
end
