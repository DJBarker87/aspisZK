import NLQ_SnapshotData
set_option autoImplicit false
noncomputable section
namespace NLQ_CheckpointRead
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- The zero-check's own extent clause is discharged at the SAME successful
checkpoint data read, before require_zero is entered. No all-zero, child
success, native endpoint or independent snapshot assumption is supplied. -/
theorem at_site (e : Entry) (ops : AdapterRw.Ops) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot 2 1768 1768)=.ok (.Ok bytes)) :
 bytes=e.buffers (e.handles 2).1 ∧ bytes.val.length=1768 ∧ bytes.val.length≤4096 := by
 obtain ⟨same,h⟩ := NLQ_SnapshotData.returned e ops 2 1768 1768 bytes read
 have size : bytes.val.length=1768 := by
  rw [same]
  exact h.elim id id
 exact ⟨same,size,by omega⟩
#print at_site
#print axioms at_site
end NLQ_CheckpointRead
