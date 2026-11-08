import NMX_R9_ArgsNative241
import NMX_R9_ValidateUse241
import NMX_R9_RelReplay241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_Head241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply id)
  (NMX_R8_Factor241.head (NMX_R8_Std241.ops env) (NMX_R9_Children241.grouped choices) p accounts data slot)
  (NMX_R9_RelReplay241.replay (NMX_R9_ArgsNative241.args p accounts data slot)) := by
 rw [NMX_R9_HeaderFactor241.factor]
 unfold NMX_R9_HeaderFactor241.source
 rw [NMX_R8_MagicCheck.full,NMX_R9_ArgsNative241.count]
 unfold NMX_R9_RelReplay241.replay
 change Simulates _ _ (RSL.RS.seq (RSL.RS.check
  (((NMS_R2N_RSLPoolCarriers.accounts accounts).length != 7) ||
   decide ((NMS_R2N_RSLScalars.bytes data).length < 4) ||
   (NMS_R2N_RSLScalars.bytes data).take 4 != RSL.REQUEST_MAGIC) .invalidInstructionData)
  (RSL.RS.bind (RSL.TX2_242.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed
   (NMX_R5_Native242.args p accounts data slot))
   (fun v => NMX_R8_After241.model v (NMS_R2N_RSLPoolCarriers.accounts accounts))))
 rw [Bool.or_assoc]
 cases badCount : ((NMS_R2N_RSLPoolCarriers.accounts accounts).length != 7) with
 | true =>
   change Simulates _ (RSL.Spec.pure (.Err .InvalidInstructionData : Reply))
    (RSL.RS.seq (RSL.RS.check true .invalidInstructionData) _)
   rw [RSL.RS.check_true,RSL.RS.seq_throw]
   exact NMS_R2N_Interpreted.pure _ _
 | false =>
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure _) _)
    (RSL.RS.seq (RSL.RS.check _ .invalidInstructionData) _)
   rw [RSL.Spec.bind_pure]
   cases badMagic : (decide ((NMS_R2N_RSLScalars.bytes data).length < 4) ||
    (NMS_R2N_RSLScalars.bytes data).take 4 != RSL.REQUEST_MAGIC) with
   | true =>
     change Simulates _ (RSL.Spec.pure (.Err .InvalidInstructionData : Reply))
      (RSL.RS.seq (RSL.RS.check true .invalidInstructionData) _)
     rw [RSL.RS.check_true,RSL.RS.seq_throw]
     exact NMS_R2N_Interpreted.pure _ _
   | false =>
     change Simulates _ (NMX_R9_ValidateUse241.source env choices p accounts data slot)
      (RSL.RS.seq (RSL.RS.check false .invalidInstructionData) _)
     rw [RSL.RS.check_false,RSL.RS.seq_pure]
     exact NMX_R9_ValidateUse241.full env choices p accounts data slot
#print axioms full
end NMX_R9_Head241
end
