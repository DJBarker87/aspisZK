import NMX_R5_PrefixSource242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Native242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def args (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.TX2_242.Args :=
 ⟨NMS_R2N_RSLScalars.b32 program,NMS_R2N_RSLPoolCarriers.accounts accounts,
  NMS_R2N_RSLScalars.bytes data,NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot⟩

/-- Full source meaning at every native input, including clone/allocation stops,
source errors and all ordered child events. No returned-only premise. -/
theorem full (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices) program accounts data slot)
  (RSL.TX2_242.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed (args program accounts data slot)) := by
 change Simulates _ (NMS_R2N_242Code.body _ _ _ _ _ _) _
 rw [← NMS_R2Code242Factor.source,← NMS_R2RequestFactor242.source,NMX_R5_PrefixSource242.full]
 change Simulates _ _ (RSL.RS.seq
  (RSL.RS.check ((NMS_R2N_RSLScalars.bytes data).length != RSL.REQUEST_BYTES) .invalidInstructionData)
  (NMX_R5_Decode242.model (NMS_R2N_RSLScalars.b32 program) (NMS_R2N_RSLPoolCarriers.accounts accounts)
   (NMS_R2N_RSLScalars.bytes data) (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot)))
 unfold NMX_R5_PrefixSource242.body
 rw [NMX_R5_Size242.guard]
 split
 · rename_i reject
   rw [reject,RSL.RS.check_true,RSL.RS.seq_throw]
   exact NMS_R2N_Interpreted.pure _ _
 · rename_i accept
   have eqfalse : ((NMS_R2N_RSLScalars.bytes data).length != RSL.REQUEST_BYTES) = false := by
    cases h : ((NMS_R2N_RSLScalars.bytes data).length != RSL.REQUEST_BYTES) <;> simp_all
   rw [eqfalse,RSL.RS.check_false,RSL.RS.seq_pure]
   exact NMX_R5_Decode242.full choices program accounts data slot
#print axioms full
end NMX_R5_Native242
end
