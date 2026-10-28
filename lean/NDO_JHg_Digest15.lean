import JHg_AuditLane
import NDO_JFt_Digest15
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest15
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value JHb_DataLane.bytes
def window := JHg_FieldRead.segment JHb_DataLane.value 544 32
theorem same : window=JFu_PublicDigest15.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 544).take 32=JFu_PublicDigest15.bytes
  rw [JHg_AuditLane.frontier_13];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest15.value) := by
  rw [same];exact JFt_Digest15.local_call
#print axioms source
end AspisR1.JHg_Digest15
