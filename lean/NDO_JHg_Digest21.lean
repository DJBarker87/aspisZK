import JHg_AuditLane
import NDO_JFt_Digest21
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest21
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value JHb_DataLane.bytes
def window := JHg_FieldRead.segment JHb_DataLane.value 736 32
theorem same : window=JFu_PublicDigest21.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 736).take 32=JFu_PublicDigest21.bytes
  rw [JHg_AuditLane.frontier_19];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest21.value) := by
  rw [same];exact JFt_Digest21.local_call
#print axioms source
end AspisR1.JHg_Digest21
