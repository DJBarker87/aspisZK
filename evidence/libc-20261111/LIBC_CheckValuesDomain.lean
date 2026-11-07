import LIBC_Bytes
import NFU_CompactLeaves
set_option autoImplicit false
noncomputable section
namespace LIBC_CheckValuesDomain
open Aeneas Aeneas.Std Result
/-- Rev3 R4, literally the CLOSED179 compact_check at the supplied byte
argument. No implicit canonicality or successful-expansion premise is added. -/
def checkValuesDom (bytes : RSL.Bytes) : Prop :=
 NFU_Retarget.compact.check_values (LIBC_Bytes.raw bytes) = ok (.Ok ())
theorem native (bytes : Slice U8) :
 checkValuesDom (LIB_Carriers.bytes bytes) ↔
 NFU_Retarget.compact.check_values bytes = ok (.Ok ()) := by
 unfold checkValuesDom
 rw [LIBC_Bytes.from_native]
#print axioms native
end LIBC_CheckValuesDomain
