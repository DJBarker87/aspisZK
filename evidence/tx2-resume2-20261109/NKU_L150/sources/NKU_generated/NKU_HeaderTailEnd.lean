import NKU_HeaderPrefix
import NKU_EndArithmetic
import NKU_Success
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderTailEnd
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Only ONE any result is abstracted; no general proof-search loop. -/
theorem fixed (bytes : Slice U8) (size : bytes.val.length=1768)
 (next : U8) (it : core.slice.iter.Iter U8) :
 NKU_Success.Ensures (NKU_HeaderPrefix.tail bytes next it) (fun pair=>pair.2=1736#usize) := by
 have lenEq : Slice.len bytes=1768#usize := UScalar.eq_of_val_eq size
 unfold NKU_HeaderPrefix.tail
 simp only [lenEq,NKU_EndArithmetic.wrap,NKK_LogReduce.lift_ok_bind,NJU_Log.prod_cases]
 apply NKU_Success.bind
 rintro ⟨hit,rest⟩
 cases hit with
 | false => exact NKU_Success.pure _ _ rfl
 | true => exact NKU_Success.reject _ _
#print axioms fixed
end NKU_HeaderTailEnd
