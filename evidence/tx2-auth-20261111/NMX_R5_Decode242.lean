import NMX_R5_Request242
import NMS_R2DecoderImage
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Decode242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def source (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :=
 NMS_R2N_RawTry.literal (liftResult (NMS_R2DecoderImage.value data))
  (fun q => NMS_R2RequestFactor242.afterRequest (NMS_R2N_Native242Children.children false)
   (NMX_R4_NMS233.typed choices) program accounts slot q)

def model (program : RSL.B32) (accounts : List RSL.OwnedAccount)
 (data : RSL.Bytes) (slot : Except RSL.ProgramError UInt64) :=
 RSL.RS.bind (RSL.RS.ofOption (LIBB_PoolLib.library.decodeRequest data) .invalidInstructionData)
  (fun q => NMX_R5_Request242.model q program accounts slot)

theorem full (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (source choices program accounts data slot)
  (model (NMS_R2N_RSLScalars.b32 program) (NMS_R2N_RSLPoolCarriers.accounts accounts)
   (NMS_R2N_RSLScalars.bytes data) (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot)) := by
 unfold source model
 apply NMS_R2N_RawTry.simulates id NMX_R5_AfterAuth242.value
 · exact NMS_R2DecoderImage.full data
 · intro q
   exact NMX_R5_Request242.full choices program accounts q slot
#print axioms full
end NMX_R5_Decode242
end
