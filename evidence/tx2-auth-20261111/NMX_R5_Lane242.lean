import NMX_R5_AfterAuth242
import LIBB_PoolDecoders
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Lane242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

theorem nullifier (q : LIBB_PoolCarriers.Request) :
 liftResult (NMS_RequestModels.nullifier q.«public») = RSL.Spec.pure (LIBB_PoolDecoders.nullifier q) := by
 unfold NMS_RequestModels.nullifier LIBB_PoolDecoders.nullifier
 cases q.«public» <;> rfl

def mapped (d : LIBB_NullifierBytes.Digest) : Result (core.result.Result U8 solana_program_error.ProgramError) := do
 let r ← NMS_RequestModels.outputLane d
 core.result.Result.map_err
  r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError r ()

theorem full (d : LIBB_NullifierBytes.Digest) :
 Simulates (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u8)
  (liftResult (mapped d))
  (RSL.RS.ofOption (LIBB_PoolLib.library.outputLane (LIBB_NullifierBytes.key d)) .invalidInstructionData) := by
 unfold mapped
 rw [NMS_R2LaneModel.source,bind_tc_ok]
 change Simulates _ _ (RSL.RS.ofOption
  (match LIBB_NullifierBytes.digest (LIBB_NullifierBytes.key d) with
   | none => none
   | some x => LIBB_V1DecoderValues.asOption NND_Carrier.byte (NFY_NBN_OutputLane.result x)) _)
 rw [LIBB_NullifierBytes.roundtrip]
 unfold NMS_R2LaneModel.result
 cases h : NFY_NBN_OutputLane.result d with
 | Err e =>
   simp only [h,LIBB_V1DecoderValues.asOption]
   change Simulates _ (RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidInstructionData : core.result.Result U8 solana_program_error.ProgramError))
    (RSL.Spec.pure (Except.error RSL.ProgramError.invalidInstructionData : Except RSL.ProgramError UInt8))
   exact NMS_R2N_Interpreted.pure _ _
 | Ok lane =>
   simp only [h,LIBB_V1DecoderValues.asOption]
   change Simulates _ (RSL.Spec.pure (core.result.Result.Ok lane : core.result.Result U8 solana_program_error.ProgramError))
    (RSL.Spec.pure (Except.ok (NMS_R2N_RSLScalars.u8 lane) : Except RSL.ProgramError UInt8))
   exact NMS_R2N_Interpreted.pure _ _
#print axioms nullifier
#print axioms full
end NMX_R5_Lane242
end
