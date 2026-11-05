import NHW_WriterReplies
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_SourceSelection
open Aeneas Aeneas.Std Result
/-- F3V's circle selection already holds in the headline installation. -/
theorem fixed {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 F3V_Install.configuration (NHW_DeployedQuery.configuration missing err r)=
 NHW_DeployedQuery.configuration missing err r := by
 have h : F3M_CircleSource.install (NHW_DeployedQuery.configuration missing err r).boundaries=
   (NHW_DeployedQuery.configuration missing err r).boundaries := by
   rw [show (NHW_DeployedQuery.configuration missing err r).boundaries=IDa_Deployed.boundaries r from
     (IDa_Deployed.selected_fields missing err r).2.1]
   rfl
 unfold F3V_Install.configuration
 rw [h]
#print axioms fixed
end AspisR1.NHW_SourceSelection
