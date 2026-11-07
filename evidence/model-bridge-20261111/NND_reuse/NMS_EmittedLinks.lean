import NMS_EmittedValidate
set_option autoImplicit false
noncomputable section
namespace NMS_EmittedLinks
open Aeneas Aeneas.Std Result AdapterRw
/-- Canonical interpretation of the freshly emitted Vec/slice getter. Both
ProgramError and the entire successful slice are kept; no Kani buffer model. -/
theorem getter (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) :
 NMS_Emitted.get ops a = r1_pool_adapter.owned.OwnedAccount.data ops a := rfl
/-- Control/value transport ONLY. This does not establish a233 packet, an
opaque child law, an ownership refinement or a positive row root. -/
theorem validate (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_Emitted.validate ops (r1_pool_adapter.owned.authenticate_asq8_accounts ops)
  program accounts data slot =
 r1_pool_adapter.owned.validate_asq8 ops program accounts data slot := rfl
#print axioms getter
#print axioms validate
end NMS_EmittedLinks
