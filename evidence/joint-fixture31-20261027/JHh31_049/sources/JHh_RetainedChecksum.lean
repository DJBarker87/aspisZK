import JHh_ImageIdentity
set_option autoImplicit false
namespace AspisR1.JHh_RetainedChecksum
open Aeneas Aeneas.Std Result
/-- Exact last 32 retained bytes; independent of source-writer identity. -/
theorem suffix : JFx_NativeBytes.checkpoint.val.drop 1736=JFo_AuthBytes.checksum.val := by
  have h := JFo_AuthBytes.checksum_selected
  change (JFx_NativeBytes.checkpoint.val.drop 1736).take 32=_ at h
  rw [List.take_of_length_le (by
    rw [List.length_drop,JFx_NativeBytes.checkpointBytes_length]
    decide)] at h
  exact h
#print axioms suffix
/-- SAME-body equality determines the actual checksum request. -/
theorem request (body : Slice U8)
    (identity : body.val=JFx_NativeBytes.checkpoint.val.take 1736) :
    AspisR1Stage2.WireTx2.checksumParts body=JFn_HashBoundary.checksumParts := by
  have same : body=JFq_Range.segment 0 1736 (by decide) := by
    apply Subtype.ext
    simpa only [JFq_Range.segment,List.drop_zero] using identity
  rw [same]
  rfl
#print axioms request
end AspisR1.JHh_RetainedChecksum
