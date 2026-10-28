import JHg_AuditLane
import NDO_JFt_Digest06
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest06
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value
def window := JHg_FieldRead.segment JHb_DataLane.value 256 32
theorem same : window=JFu_PublicDigest06.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 256).take 32=JFu_PublicDigest06.bytes
  rw [JHg_AuditLane.frontier_4];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest06.value) := by
  rw [same];exact JFt_Digest06.local_call
#print axioms source
end AspisR1.JHg_Digest06
