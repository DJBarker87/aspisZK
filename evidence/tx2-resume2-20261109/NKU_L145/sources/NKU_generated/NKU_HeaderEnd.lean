import NKU_EndArithmetic
import NKU_Success
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderEnd
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem fixed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (size : bytes.val.length=1768) :
 NKU_Success.Ensures (NKU_HeaderValue.value d bytes .S2) (fun pair=>pair.2=1736#usize) := by
 have lenEq : Slice.len bytes=1768#usize := UScalar.eq_of_val_eq size
 unfold NKU_HeaderValue.value
 simp only [lenEq,NKU_EndArithmetic.wrap,NKU_HeaderSize.size,NKK_LogReduce.lift_ok_bind,NJU_Log.prod_cases]
 repeat' first
 | (exact NKU_Success.reject _ _)
 | (apply NKU_Success.pure;rfl)
 | (apply NKU_Success.bind;intro value)
 | split
theorem returned {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (reply : U8 × Usize)
 (actual : (NKU_HeaderValue.value d bytes .S2).result=ok (.Ok reply)) : reply.2=1736#usize :=
 fixed d bytes (NKU_HeaderDomain.length d bytes reply actual) reply actual
#print axioms fixed
#print axioms returned
end NKU_HeaderEnd
