import NLE_OwnedFine
import NLM_DeployedOps
set_option autoImplicit false
noncomputable section
namespace NMK_241Source
open Aeneas Aeneas.Std AspisR1 AspisR1.IDa_Deployed
/-- Read-only reuse of the predecessor source transcription at the headline's
named installation. This is source support only: neither full233/242 packets
nor a native241 parent producer are inferred from the equality. -/
theorem source {CoreError : Type} (missing : Uninstalled CoreError) (indexError : CoreError)
 (reservation : NP6_StdModel.Reservation) (initial : NLE_Owned.State) :
 (NLE_OwnedFine.G (NLM_DeployedOps.ops missing indexError reservation) initial).result =
 AdapterRw.r1_pool_adapter.owned.stage2_owned (NLM_DeployedOps.ops missing indexError reservation)
 initial.frame.program initial.frame.accounts initial.frame.data initial.frame.slot :=
 NLE_OwnedFine.source (NLM_DeployedOps.ops missing indexError reservation) initial
#print source
#print axioms source
end NMK_241Source
