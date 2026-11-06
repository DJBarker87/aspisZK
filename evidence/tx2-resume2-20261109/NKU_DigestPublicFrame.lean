import NKU_Core
import NKU_DigestPublic
set_option autoImplicit false
noncomputable section
namespace NKU_DigestPublicFrame
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Exact read-only frame of one native digest cut on its SAME live state. -/
theorem preserved {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) :
 NKU_Core.Preserves (NKU_DigestPublic.run d hash) := by
 intro s out actual
 have law : NKU_Success.Ensures (NKU_DigestPublic.run d hash s)
   (fun pair=>NKU_Core.value pair.2=NKU_Core.value s) := by
  unfold NKU_DigestPublic.run NKK_DigestSource.model
  apply NKU_Success.bind
  intro v0
  apply NKU_Success.bind
  intro v1
  apply NKU_Success.bind
  intro v2
  split
  · exact NKU_Success.pure _ _ rfl
  · exact NKU_Success.reject _ _
 exact law ((),out) actual
#print axioms preserved
end NKU_DigestPublicFrame
