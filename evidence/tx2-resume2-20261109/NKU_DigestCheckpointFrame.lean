import NKU_Core
import NKU_DigestCheckpoint
set_option autoImplicit false
noncomputable section
namespace NKU_DigestCheckpointFrame
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Exact read-only frame of one native digest cut on its SAME live state. -/
theorem preserved {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) («end» : Usize) :
 NKU_Core.Preserves (NKU_DigestCheckpoint.run d hash «end») := by
 intro s out actual
 have law : NKU_Success.Ensures (NKU_DigestCheckpoint.run d hash «end» s)
   (fun pair=>NKU_Core.value pair.2=NKU_Core.value s) := by
  unfold NKU_DigestCheckpoint.run NKK_DigestSource.model
  apply NKU_Success.bind
  intro v0
  apply NKU_Success.bind
  intro v1
  apply NKU_Success.bind
  intro v2
  apply NKU_Success.bind
  intro v3
  apply NKU_Success.bind
  intro v4
  split
  · exact NKU_Success.pure _ _ rfl
  · exact NKU_Success.reject _ _
 exact law ((),out) actual
#print axioms preserved
end NKU_DigestCheckpointFrame
