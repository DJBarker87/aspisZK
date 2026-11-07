import LIBC_PreparedDomain
import LIBC_ExpandTrace
import LIBC_CheckValuesDomain
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedR4
open Aeneas Aeneas.Std AspisR1PublicPreparation
/-- Same compact argument, same output buffer and all byte coordinates. The
source trace needed by179 is a theorem of the464/928 expansion model, not a
success premise on an unrelated or independently selected child. -/
theorem expanded (v : verifier.View) (compact before : Slice U8) (src : compact.val.length=464)
 (dst : before.val.length=928) (checked : NFU_Retarget.compact.check_values compact=.ok (.Ok ()))
 (same : v.y1=LIBC_ExpandValuesModel.output compact before) :
 LIBC_PreparedDomain.Expanded v := by
 refine ⟨compact,before,src,dst,checked,?_⟩
 rw [same]
 have trace := LIBC_ExpandTrace.trace compact before (by omega) (by omega) (by omega)
 simpa only [src] using trace
#print axioms expanded
end LIBC_PreparedR4
