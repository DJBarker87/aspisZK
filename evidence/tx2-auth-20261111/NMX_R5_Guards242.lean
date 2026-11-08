import NMX_R5_Slot242
import NMS_R2Gated242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Guards242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def model (q : LIBB_PoolCarriers.Request) (program : RSL.B32)
 (accounts : List RSL.OwnedAccount) (slot : Except RSL.ProgramError UInt64) :=
 RSL.RS.bind (RSL.RS.ofOption (LIBB_PoolLib.library.outputLane (LIBB_PoolLib.library.reqNullifier q))
   .invalidInstructionData) (fun lane => NMX_R5_Slot242.model q program accounts lane slot)

theorem factor (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (q : LIBB_PoolCarriers.Request) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_R2Gated242.afterGuards (NMS_R2N_Native242Children.children false)
  (NMX_R4_NMS233.typed choices) program accounts slot q =
 NMS_R2N_RawTry.literal (liftResult (NMX_R5_Lane242.mapped (LIBB_PoolDecoders.nullifier q)))
  (fun lane => NMX_R5_Slot242.source choices program accounts q lane slot) := by
 unfold NMS_R2Gated242.afterGuards NMS_R2N_Native242Children.children
 simp only [Bind.bind,RSL.Spec.bind_pure]
 rw [NMX_R5_Lane242.nullifier]
 simp only [Bind.bind,RSL.Spec.bind_pure,NMS_R2LaneModel.full]
 unfold NMS_R2N_RawTry.literal NMX_R5_Slot242.source
 simp only [Bind.bind]
 rw [NMX_R5_LaneSource242.mapped]
 apply congrArg (RSL.Spec.bind _)
 funext laneReply
 apply congrArg (RSL.Spec.bind _)
 funext laneFlow
 cases laneFlow with
 | Break residual => rfl
 | Continue lane =>
   apply congrArg (RSL.Spec.bind _)
   funext slotFlow
   cases slotFlow with
   | Break residual => rfl
   | Continue current =>
     apply congrArg (RSL.Spec.bind _)
     funext authReply
     apply congrArg (RSL.Spec.bind _)
     funext authFlow
     cases authFlow <;> rfl

theorem full (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (q : LIBB_PoolCarriers.Request) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (NMS_R2Gated242.afterGuards (NMS_R2N_Native242Children.children false)
   (NMX_R4_NMS233.typed choices) program accounts slot q)
  (model q (NMS_R2N_RSLScalars.b32 program) (NMS_R2N_RSLPoolCarriers.accounts accounts)
   (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot)) := by
 rw [factor]
 unfold model
 apply NMS_R2N_RawTry.simulates NMS_R2N_RSLScalars.u8 NMX_R5_AfterAuth242.value
 · exact NMX_R5_Lane242.full _
 · intro lane
   exact NMX_R5_Slot242.full choices program accounts q lane slot
#print axioms factor
#print axioms full
end NMX_R5_Guards242
end
