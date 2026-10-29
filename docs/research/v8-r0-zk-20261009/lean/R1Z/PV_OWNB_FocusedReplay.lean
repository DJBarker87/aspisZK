import R1Z.PV_OWNB_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWNB_FocusedReplay
open PV_OWNB_Cursor PV_OWN_Link
/-- Frozen model closure replay. No native restoration conclusion is asserted. -/
theorem replay (q : Cursor) (keep : Link → Bool) (h:Valid q) :
 let final:=PV_OWNB_SnapshotFold.run keep (q.length-q.read) q
 Valid final ∧ final.read=q.length ∧
 PV_OWNB_Prefix.values final=PV_OWNB_Prefix.values q++
 (PV_OWNB_ValueFold.input q.source q.read (q.length-q.read)).filter keep :=
 PV_OWNB_SnapshotResult.complete q keep h
#print axioms replay
#print axioms R1Z.PV_OWNB_ActualResult.complete
#print axioms R1Z.PV_OWNB_CursorTransfer.owned
#print axioms R1Z.PV_OWNB_CursorCleanup.positive
#print axioms R1Z.PV_OWNB_NoDoubleCleanup.no_second_call
#print axioms R1Z.PV_OWNB_CleanupRetired.dead
end R1Z.PV_OWNB_FocusedReplay
