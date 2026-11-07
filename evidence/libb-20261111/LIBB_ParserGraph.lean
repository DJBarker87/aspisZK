import LIBB_EnvValues
set_option autoImplicit false
noncomputable section
namespace LIBB_ParserGraph
open Aeneas Aeneas.Std AspisR1
/-- The complete parser split, including parser fail/div/rejection. A parser
Ok is an output branch of the CLOSED emitted parser, never a caller premise. -/
theorem source (env : RSL.Env) (pub proof ck : Slice U8) :
 LIBB_Tx2EnvCode.code env pub proof ck =
 match NLE_ParseInstall.parse proof with
 | .fail e=>.fail e
 | .div=>.div
 | .ok (.Err e)=>.ok (.Err e)
 | .ok (.Ok _)=>LIBB_Tx2EnvCode.common env pub proof ck := by
 unfold LIBB_Tx2EnvCode.code
 cases h:NLE_ParseInstall.parse proof with
 | fail e=>rfl
 | div=>rfl
 | ok v=>cases v <;> rfl
#print axioms source
end LIBB_ParserGraph
end
