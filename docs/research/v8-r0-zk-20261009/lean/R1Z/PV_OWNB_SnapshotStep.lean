import R1Z.PV_OWNB_ReadSnapshot
import R1Z.PV_OWNB_ActualSinkValid
set_option autoImplicit false
namespace R1Z.PV_OWNB_SnapshotStep
open PV_OWNB_Cursor PV_OWN_Link
/-- Read the old cell before advancing and writing, retaining optional padding. -/
def step (keep : Link → Bool) (q : Cursor) : Cursor :=
 if keep (q.source q.read) then
  PV_OWNB_ActualSink.sink (advance q) (q.source q.read) (PV_OWNB_ReadSnapshot.bytes q)
 else advance q

theorem valid (keep : Link → Bool) (q : Cursor) (h:Valid q) (more:q.read<q.length) :
 Valid (step keep q) := by
 have ha:=PV_OWNB_CursorRead.advance q h more
 unfold step
 split
 · apply PV_OWNB_ActualSinkValid.valid _ _ _ ha _ (PV_OWNB_ReadSnapshot.represented q h more)
   change q.written<q.read+1
   unfold Valid at h
   omega
 · exact ha

theorem advances (keep : Link → Bool) (q : Cursor) :
 (step keep q).read=q.read+1 := by
 unfold step
 split <;> rfl

theorem length (keep : Link → Bool) (q : Cursor) :
 (step keep q).length=q.length := by
 unfold step
 split <;> rfl
attribute [local irreducible] step
#print axioms valid
#print axioms advances
#print axioms length
end R1Z.PV_OWNB_SnapshotStep
