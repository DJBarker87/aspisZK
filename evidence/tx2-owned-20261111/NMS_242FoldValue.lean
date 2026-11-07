import NMS_RowSpec233
import NMS_EmittedLinks
set_option autoImplicit false
noncomputable section
namespace NMS_242FoldValue
open Aeneas Aeneas.Std AdapterRw
abbrev World := NMS_RowSpec233.World
/-- The actual recorded child occurrence is selected at its SAME five arguments
and the SAME external world. No independently chosen successful reply. -/
def authValue {Ambient : Type} (native : NMS_RowSpec233.Native Ambient)
 (before : World Ambient) : NMS_Emitted.AuthCall := fun program accounts pool lane slot =>
 NMS_RowSpec233.eraseValue (native ⟨program,accounts,pool,lane,slot⟩ before)

/-- Full Result fold of the freshly emitted242 body, including rejection,
clone failure and divergence. This is the value projection of the parameterized
fold, not a complete observable root or a CLOSED-row claim. -/
theorem emitted {Ambient CoreError : Type}
 (missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
 (reservation : AspisR1.NP6_StdModel.Reservation)
 (owners : NMS_RowSpec233.Args → List Nat) (native : NMS_RowSpec233.Native Ambient)
 (child : NMS_RowSpec233.RowSpec_233 missing indexError reservation owners native)
 (before : World Ambient) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_Emitted.validate (NLM_DeployedOps.ops missing indexError reservation)
  (authValue native before) program accounts data slot =
 r1_pool_adapter.owned.validate_asq8 (NLM_DeployedOps.ops missing indexError reservation)
  program accounts data slot := by
 have same : authValue native before =
   r1_pool_adapter.owned.authenticate_asq8_accounts
    (NLM_DeployedOps.ops missing indexError reservation) := by
  funext p a pool lane current
  exact (child ⟨p,a,pool,lane,current⟩ before).2
 rw [same]
 exact NMS_EmittedLinks.validate _ _ _ _ _
#print emitted
#print axioms emitted
end NMS_242FoldValue
