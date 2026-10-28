import JHg_AuditLane
import NDO_JFt_Digest12
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest12
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value
def window := JHg_FieldRead.segment JHb_DataLane.value 448 32
theorem same : window=JFu_PublicDigest12.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 448).take 32=JFu_PublicDigest12.bytes
  rw [JHg_AuditLane.frontier_10];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest12.value) := by
  rw [same];exact JFt_Digest12.local_call
#print axioms source
end AspisR1.JHg_Digest12
