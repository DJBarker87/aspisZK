import NKU_HeaderTailEnd
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderEnd
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem fixed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (size : bytes.val.length=1768) :
 NKU_Success.Ensures (NKU_HeaderValue.value d bytes .S2) (fun pair=>pair.2=1736#usize) := by
 rw [NKU_HeaderPrefix.source]
 apply NKU_Success.bind
 intro reply
 rw [NKK_Try.branch]
 cases reply with
 | Err err => exact NKU_Success.reject _ _
 | Ok pair => exact NKU_HeaderTailEnd.fixed bytes size pair.1 pair.2
theorem returned {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (reply : U8 × Usize)
 (actual : (NKU_HeaderValue.value d bytes .S2).result=ok (.Ok reply)) : reply.2=1736#usize :=
 fixed d bytes (NKU_HeaderDomain.length d bytes reply actual) reply actual
#print axioms fixed
#print axioms returned
end NKU_HeaderEnd
