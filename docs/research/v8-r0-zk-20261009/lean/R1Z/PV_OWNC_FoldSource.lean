import R1Z.PV_OWNC_ReadPointer
set_option autoImplicit false
namespace R1Z.PV_OWNC_FoldSource
open PV_OWNB_Cursor PV_OWN_Link
/-- Source try_fold reads tmp, advances ptr, calls filter_try_fold, then
write_in_place_with_drop. The active-byte snapshot is taken before the store. -/
def sourceStep (keep : Link → Bool) (q : Cursor) : Cursor :=
 let tmp:=q.source q.read
 let bytes:=PV_OWNB_ReadSnapshot.bytes q
 let advanced:=advance q
 if keep tmp then PV_OWNB_ActualSink.sink advanced tmp bytes else advanced

theorem step_binding (keep : Link → Bool) (q : Cursor) :
 sourceStep keep q=PV_OWNB_SnapshotStep.step keep q := rfl

theorem valid (keep : Link → Bool) (q : Cursor) (h:Valid q) (more:q.read<q.length) :
 Valid (sourceStep keep q) := by
 rw [step_binding]
 exact PV_OWNB_SnapshotStep.valid keep q h more
#print axioms step_binding
#print axioms valid
end R1Z.PV_OWNC_FoldSource
