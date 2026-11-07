import NMX_MasterValue
import NMX_CheckpointValue
set_option autoImplicit false
noncomputable section
namespace NMX_DecoderErrors
open Aeneas Aeneas.Std AdapterRw

theorem master (b : Slice U8) (error : solana_program_error.ProgramError)
 (reply : NMX_MasterValue.decoded b = .Err error) : error = .InvalidAccountData := by
 unfold NMX_MasterValue.decoded at reply
 cases h : NJQ_Carrier.master_result (NMX_MasterValue.raw b) with
 | Ok value => simp only [h,NKF_BoxModel.tail] at reply; cases reply
 | Err e => simp only [h,NKF_BoxModel.tail] at reply; exact (core.result.Result.Err.inj reply).symm

theorem checkpoint (b : Slice U8) (error : solana_program_error.ProgramError)
 (reply : NMX_CheckpointValue.decoded b = .Err error) : error = .InvalidAccountData := by
 unfold NMX_CheckpointValue.decoded at reply
 cases h : NJQ_Carrier.checkpoint_result (NMX_CheckpointValue.raw b) with
 | Ok value => simp only [h,NKF_BoxModel.tail] at reply; cases reply
 | Err e => simp only [h,NKF_BoxModel.tail] at reply; exact (core.result.Result.Err.inj reply).symm
#print axioms master
#print axioms checkpoint
end NMX_DecoderErrors
end
