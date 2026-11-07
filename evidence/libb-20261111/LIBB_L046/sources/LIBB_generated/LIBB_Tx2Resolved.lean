import LIBB_Tx2Reservation
import LIBB_HashModel
import NMN_064
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2Resolved
open Aeneas Aeneas.Std AspisR1
abbrev Reply := core.result.Result Unit VTop_Stages.verifier.Error
/-- Deterministic source value with EVERY fallible reservation read from the
same Env binder. This is resolved-value support, not the completed tx2auth
Spec: digest chronology and independent stopped-C04 prefixes remain explicit
obligations and are not replaced by an empty trace. -/
def common (env : RSL.Env) (pub proof ck : Slice U8) : Result Reply :=
 let r := LIBB_Tx2Reservation.reservation env
 NJJ_Common.run r r (NLP_NativeMerkle.action (LIBB_HashModel.H env))
  (NLB_Parent.finish r) (LIBB_HashModel.digest env) pub proof ck () none

def observed (env : RSL.Env) (pub proof ck : Slice U8) :=
 let r := LIBB_Tx2Reservation.reservation env
 NJU_CommonObserved.run r r (NLP_NativeMerkle.action (LIBB_HashModel.H env))
  (NLB_Parent.finish r) (LIBB_HashModel.digest env) pub proof ck () none

def code (env : RSL.Env) (pub proof ck : Slice U8) : Result Reply := do
 let parsed ← NLE_ParseInstall.parse proof
 match parsed with | .Err e => .ok (.Err e) | .Ok _ => common env pub proof ck

theorem source_result (env : RSL.Env) (pub proof ck : Slice U8) :
 (observed env pub proof ck).result = common env pub proof ck :=
 NJU_CommonObserved.source _ _ _ _ _ _ _ _ ()

/-- Same-source parser association from the CLOSED064 root; no parser
success or arbitrary operation dictionary is supplied by the caller. -/
theorem parser (proof : Slice U8) :
 NLE_ParseInstall.parse proof =
 NJS_Parse.map NLE_ParseInstall.reply (NJS_Parse.map NJS_Parse.reply
  (NJS_Extract.verifier.candidate.parse_shape
   Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof)) :=
 NLE_ParseInstall.emitted proof
#print axioms source_result
#print axioms parser
end LIBB_Tx2Resolved
end
