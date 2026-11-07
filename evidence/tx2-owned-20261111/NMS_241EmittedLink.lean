import NMS_Emitted241
import NMS_EmittedLinks
set_option autoImplicit false
noncomputable section
namespace NMS_241EmittedLink
open Aeneas Aeneas.Std Result AdapterRw
/-- Complete value/control equality for the fresh241 canonical-owner replay.
No observer comparison, Kani buffer, or simplified ProgramError is used. This
is source support, not the native observable/independent-stop row root. -/
theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_Emitted.stage2 ops (r1_pool_adapter.owned.authenticate_asq8_accounts ops)
  program accounts data slot = r1_pool_adapter.owned.stage2_owned ops program accounts data slot := by
 unfold NMS_Emitted.stage2 r1_pool_adapter.owned.stage2_owned
 simp only [NMS_EmittedLinks.validate,NMS_EmittedLinks.getter,bind_tc_ok]
 rfl
#print source
#print axioms source
end NMS_241EmittedLink
