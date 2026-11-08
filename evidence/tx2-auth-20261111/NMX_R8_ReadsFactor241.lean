import NMX_R8_Children241
import NMX_R8_Factor241
import NMX_R8_Std241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_ReadsFactor241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def source (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8) :=
 if Slice.len proof != 58295#usize then
  RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData :
   core.result.Result Unit solana_program_error.ProgramError)
 else NMS_R2N_RawTry.literal (NMX_R7_Encoder241.mapped v.statement)
  (fun pub => NMX_R8_Factor241.afterEncode (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices)
   v proof checkpoint 688#usize 58295#usize pub)

theorem factor (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8)
 (length : v.proof_length = 57607#usize) :
 NMX_R8_Factor241.afterReads (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) v proof checkpoint =
 source env choices v proof checkpoint := by
 unfold NMX_R8_Factor241.afterReads
 rw [NMX_R8_Std241.afterstate]
 change RSL.Spec.bind (RSL.Spec.pure 688#usize) _ = _
 rw [RSL.Spec.bind_pure,length,NMX_R8_Std241.checked]
 change RSL.Spec.bind (RSL.Spec.pure (some 58295#usize)) _ = _
 rw [RSL.Spec.bind_pure]
 change RSL.Spec.bind (RSL.Spec.pure (core.result.Result.Ok 58295#usize :
  core.result.Result Usize solana_program_error.ProgramError)) _ = _
 rw [RSL.Spec.bind_pure]
 change RSL.Spec.bind (RSL.Spec.pure (core.ops.control_flow.ControlFlow.Continue 58295#usize :
  core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible solana_program_error.ProgramError) Usize)) _ = _
 rw [RSL.Spec.bind_pure]
 unfold source NMS_R2N_RawTry.literal
 dsimp only
 cases guard : (Slice.len proof != 58295#usize) with
 | true => rfl
 | false =>
   apply congrArg (RSL.Spec.bind _)
   funext reply
   apply congrArg (RSL.Spec.bind _)
   funext flow
   cases flow <;> rfl
#print axioms factor
end NMX_R8_ReadsFactor241
end
