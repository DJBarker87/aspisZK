import JHg_AuditForest
import NDO_JFt_Digest00
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest00
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataForest.value
def window := JHg_FieldRead.segment JHg_DataForest.value 80 32
theorem same : window=JFu_PublicDigest00.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHg_DataForest.value
  change (JHg_DataForest.bytes.drop 80).take 32=JFu_PublicDigest00.bytes
  rw [JHg_AuditForest.root];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest00.value) := by
  rw [same];exact JFt_Digest00.local_call
#print axioms source
end AspisR1.JHg_Digest00
