import NMP_EmittedContext
import LIBC_ExpandValues
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ExpandValues087
open Aeneas Aeneas.Std Result NMP_prepare

def call (src before : Slice U8) : Result (core.result.Result Unit compact.CodecError × Slice U8) :=
 .ok (.Ok (),LIBC_ExpandValuesModel.output src before)
def port (r : core.result.Result Unit compact.CodecError × Slice U8) : Except LIB_VCarriers.CodecErr RSL.Bytes :=
 match r.1 with | .Ok _=>.ok (LIB_Carriers.bytes r.2) | .Err _=>.error .Length

theorem source (src before : Slice U8) (srcSize : src.val.length=464) (dstSize : before.val.length=928) :
 NFU_Retarget.compact.expand_values src before =
 .ok (.Ok (),LIBC_ExpandValuesModel.output src before) := by
 rw [LIBC_ExpandValuesModel.source src before (by omega),if_pos (by omega)]

theorem projected (src before : Slice U8) (env : RSL.Env) :
 NNG_EmittedCallGraph.resultMap port (call src before) =
 .ok (LIBC_ExpandValues.value (LIB_Carriers.bytes src,LIB_Carriers.bytes before) env) := by
 unfold call port NNG_EmittedCallGraph.resultMap LIBC_ExpandValues.value
 rw [LIBC_Bytes.from_native,LIBC_Bytes.from_native]
#print axioms source
#print axioms projected
end AspisR1.NNG_ExpandValues087
