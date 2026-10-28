import JHg_AuditLane
import NDO_JFt_Digest18
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_Digest18
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value JHb_DataLane.bytes
def window := JHg_FieldRead.segment JHb_DataLane.value 640 32
theorem same : window=JFu_PublicDigest18.window := by
  apply Subtype.ext
  unfold window JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 640).take 32=JFu_PublicDigest18.bytes
  rw [JHg_AuditLane.frontier_16];rfl
#print axioms same
theorem source : AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok JFt_Digest18.value) := by
  rw [same];exact JFt_Digest18.local_call
#print axioms source
end AspisR1.JHg_Digest18
