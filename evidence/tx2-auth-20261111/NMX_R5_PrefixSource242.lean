import NMX_R5_Decode242
import NMX_R5_Size242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_PrefixSource242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def body (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 RSL.Spec (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError) :=
 if Slice.len data != 320#usize then
  RSL.Spec.pure (.Err .InvalidInstructionData)
 else NMX_R5_Decode242.source choices program accounts data slot

theorem full (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_R2RequestFactor242.body (NMS_R2N_Native242Children.children false)
  (NMX_R4_NMS233.typed choices) program accounts data slot =
 body choices program accounts data slot := by
 unfold NMS_R2RequestFactor242.body
 rw [NMX_R5_Size242.request]
 change RSL.Spec.bind (RSL.Spec.pure 320#usize) _ = _
 rw [RSL.Spec.bind_pure]
 unfold body
 split
 · rfl
 · unfold NMX_R5_Decode242.source NMS_R2N_RawTry.literal
   obtain ⟨decoded,run⟩ := NMS_R2RequestTotal.total data
   change RSL.Spec.bind (liftResult (AspisR1.NFY_JHd_RequestNative.decode data)) _ = _
   rw [run]
   change RSL.Spec.bind (RSL.Spec.pure decoded) _ = _
   rw [RSL.Spec.bind_pure]
   unfold NMS_R2DecoderImage.value
   rw [run,bind_tc_ok]
   apply congrArg (RSL.Spec.bind _)
   funext reply
   apply congrArg (RSL.Spec.bind _)
   funext flow
   cases flow <;> rfl
#print axioms full
end NMX_R5_PrefixSource242
end
