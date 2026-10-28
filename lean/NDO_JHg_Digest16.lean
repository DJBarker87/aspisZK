import JHg_AuditLane
import NDO_JFt_Digest16
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest16
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value JHb_DataLane.bytes
def window := JHg_FieldRead.segment JHb_DataLane.value 576 32
theorem same : window=JFu_PublicDigest16.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 576).take 32=JFu_PublicDigest16.bytes
  rw [JHg_AuditLane.frontier_14];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest16.value) := by
  rw [same];exact JFt_Digest16.local_call
#print axioms source
end AspisR1.JHg_Digest16
