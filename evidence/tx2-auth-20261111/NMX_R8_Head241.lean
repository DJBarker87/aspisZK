import NMX_R8_HeaderFactor241
import NMX_R8_ValidateUse241
import NMS_R2N_RSLScalarEq
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Head241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def args (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.TX2_241.Args :=
 ⟨NMS_R2N_RSLScalars.b32 p,NMS_R2N_RSLPoolCarriers.accounts accounts,NMS_R2N_RSLScalars.bytes data,
 NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot⟩

theorem count (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 (Slice.len accounts != 7#usize) = ((NMS_R2N_RSLPoolCarriers.accounts accounts).length != 7) := by
 rw [NMS_R2N_RSLScalarEq.scalar_bne,NMX_R2_LengthGuard.value]
 simp only [NMS_R2N_RSLPoolCarriers.accounts,List.length_map]
 have seven : (7#usize).val = 7 := by scalar_tac
 rw [seven]
 by_cases same : accounts.val.length = 7 <;> simp [same]

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply id)
  (NMX_R8_Factor241.head (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) p accounts data slot)
  (NMX_R8_RelReplay241.replay choices (args p accounts data slot)) := by
 rw [NMX_R8_HeaderFactor241.factor]
 unfold NMX_R8_HeaderFactor241.source
 rw [NMX_R8_MagicCheck.full,count]
 unfold NMX_R8_RelReplay241.replay
 change Simulates _ _ (RSL.RS.seq (RSL.RS.check
  (((NMS_R2N_RSLPoolCarriers.accounts accounts).length != 7) ||
   decide ((NMS_R2N_RSLScalars.bytes data).length < 4) ||
   (NMS_R2N_RSLScalars.bytes data).take 4 != RSL.REQUEST_MAGIC) .invalidInstructionData)
  (RSL.RS.bind (NMS_R2Refine.observed (NMX_R6_Validation.validate choices)
   (NMX_R5_Native242.args p accounts data slot))
   (fun v => NMX_R8_After241.model v (NMS_R2N_RSLPoolCarriers.accounts accounts))))
 rw [Bool.or_assoc]
 cases badCount : ((NMS_R2N_RSLPoolCarriers.accounts accounts).length != 7) with
 | true =>
   rw [RSL.RS.check_true,RSL.RS.seq_throw]
   exact NMS_R2N_Interpreted.pure _ _
 | false =>
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure _) _) _
   rw [RSL.Spec.bind_pure]
   cases badMagic : (decide ((NMS_R2N_RSLScalars.bytes data).length < 4) ||
    (NMS_R2N_RSLScalars.bytes data).take 4 != RSL.REQUEST_MAGIC) with
   | true =>
     rw [RSL.RS.check_true,RSL.RS.seq_throw]
     exact NMS_R2N_Interpreted.pure _ _
   | false =>
     rw [RSL.RS.check_false,RSL.RS.seq_pure]
     exact NMX_R8_ValidateUse241.full env choices p accounts data slot
#print axioms count
#print axioms full
end NMX_R8_Head241
end
