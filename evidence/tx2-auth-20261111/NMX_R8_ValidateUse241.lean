import NMX_R8_After241
import NMX_R8_RawPath241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_ValidateUse241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library

def source (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :=
 NMS_R2N_RawTry.literal (NMX_R8_Children241.validate choices p accounts data slot)
  (fun v => NMX_R8_Factor241.afterValidate (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) v accounts)

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply id) (source env choices p accounts data slot)
  (RSL.RS.bind (NMS_R2Refine.observed (NMX_R6_Validation.validate choices)
   (NMX_R5_Native242.args p accounts data slot))
   (fun v => NMX_R8_After241.model v (NMS_R2N_RSLPoolCarriers.accounts accounts))) := by
 unfold source
 apply NMX_R8_RawPath241.full NMX_R5_AfterAuth242.value id
 · exact NMX_R8_Children241.validate_full choices p accounts data slot
 · intro actualEnv v events cut
   have seen := NMX_R8_Children241.validate_full choices p accounts data slot actualEnv _ cut
   have law := NMX_R6_Validation.root choices (NMX_R5_Native242.args p accounts data slot) actualEnv trivial
   change mapObs (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value) ⟨.ret (.Ok v),events⟩ = _ at seen
   rw [←seen] at law
   have scope := NMS_R2Facts242.successful L LIBB_PoolLib.deployed LIBB_PoolLib.scanner_extent
    _ actualEnv (NMX_R5_AfterAuth242.value v) events law
   have length : v.proof_length = 57607#usize := by
    apply UScalar.eq_of_val_eq
    have value := scope.1
    change v.proof_length.val = RSL.PROOF_BYTES at value
    rw [value]
    unfold RSL.PROOF_BYTES
    scalar_tac
   exact NMX_R8_After241.full env choices v accounts length actualEnv
#print axioms full
end NMX_R8_ValidateUse241
end
