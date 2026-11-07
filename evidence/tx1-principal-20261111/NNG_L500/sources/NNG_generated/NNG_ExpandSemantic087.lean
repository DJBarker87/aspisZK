import NMP_EmittedContext
import LIBC_ExpandSemantic
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ExpandSemantic087
open Aeneas Aeneas.Std Result NMP_prepare

def call (src _before : Slice U8) : Result (core.result.Result Unit compact.CodecError × Slice U8) :=
 .ok (.Ok (),LIBC_ExpandSemanticModel.output src)
def port (r : core.result.Result Unit compact.CodecError × Slice U8) : Except LIB_VCarriers.CodecErr RSL.Bytes :=
 match r.1 with | .Ok _=>.ok (LIB_Carriers.bytes r.2) | .Err _=>.error .Length

theorem source (src before : Slice U8) (srcSize : src.val.length=7015) (dstSize : before.val.length=13831) :
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues src before =
 .ok (.Ok (),LIBC_ExpandSemanticModel.output src) := LIBC_ExpandSemanticModel.source src before srcSize dstSize

theorem projected (src before : Slice U8) (env : RSL.Env) :
 NNG_EmittedCallGraph.resultMap port (call src before) =
 .ok (LIBC_ExpandSemantic.value (LIB_Carriers.bytes src,LIB_Carriers.bytes before) env) := by
 unfold call port NNG_EmittedCallGraph.resultMap LIBC_ExpandSemantic.value
 rw [LIBC_Bytes.from_native]
#print axioms source
#print axioms projected
end AspisR1.NNG_ExpandSemantic087
