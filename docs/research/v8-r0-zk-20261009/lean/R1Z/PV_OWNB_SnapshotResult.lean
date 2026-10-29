import R1Z.PV_OWNB_SnapshotValues
set_option autoImplicit false
namespace R1Z.PV_OWNB_SnapshotResult
open PV_OWNB_Cursor PV_OWN_Link
/-- The typed memory snapshot itself supplies the copy law. This is a complete
model filter theorem; native ptr::read/write and all later V229 stages remain. -/
theorem complete (q : Cursor) (keep : Link → Bool) (h:Valid q) :
 let final:=PV_OWNB_SnapshotFold.run keep (q.length-q.read) q
 Valid final ∧ final.read=q.length ∧
 PV_OWNB_Prefix.values final=PV_OWNB_Prefix.values q++
 (PV_OWNB_ValueFold.input q.source q.read (q.length-q.read)).filter keep := by
 have hv:=h
 unfold Valid at h
 refine ⟨PV_OWNB_SnapshotFold.valid keep _ q hv (by omega),?_,?_⟩
 · rw [PV_OWNB_SnapshotFold.advances]
   have le:=h.2.2.2.2.1
   omega
 · rw [PV_OWNB_SnapshotValues.values,PV_OWNB_ValueFold.filter]
#print axioms complete
end R1Z.PV_OWNB_SnapshotResult
