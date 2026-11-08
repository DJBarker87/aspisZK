import NMX_R7_Encoder241
import NMX_R8_Stops
set_option autoImplicit false
noncomputable section
namespace NMX_R8_CodecGroup
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
open NMX_R7_Encoder241

def representative : core.result.Result Bytes1880 AspisS6OuterNativeInstalled.Error →
 core.result.Result Bytes1880 RawError
 | .Ok bytes => .Ok bytes
 | .Err _ => .Err .WrongLength

def code (s : LIBB_PoolCarriers.Statement) : Result (core.result.Result Bytes1880 RawError) := do
 let r ← LIBB_PoolEncode.code s
 ok (representative r)

/-- The intermediate error representative is unobservable: the ACTUAL next
frozen callback is constant on every format error. It is used only inside this
block; this theorem makes no claim about the unmapped raw error payload. -/
theorem context {A : Type} (s : LIBB_PoolCarriers.Statement)
 (next : core.result.Result Bytes1880 solana_program_error.ProgramError → RSL.Spec A) :
 RSL.Spec.bind (liftResult (code s)) (fun r =>
  RSL.Spec.bind (liftResult (core.result.Result.map_err
   r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
   r ())) next) =
 RSL.Spec.bind (mapped s) next := by
 unfold code mapped RSL.Spec.map
 cases run : LIBB_PoolEncode.code s with
 | ok r =>
   cases r <;>
    simp only [bind_tc_ok,liftResult,RSL.Spec.bind_pure,representative,reply,callback]
 | fail error =>
   simp only [bind_tc_fail,liftResult,NMX_R8_Stops.panic_bind]
 | div =>
   simp only [bind_tc_div,liftResult]
   change RSL.Spec.bind NMX_R8_Stops.diverge _ =
    RSL.Spec.bind (RSL.Spec.bind NMX_R8_Stops.diverge _) _
   simp only [NMX_R8_Stops.diverge_bind]
#print axioms context
end NMX_R8_CodecGroup
end
