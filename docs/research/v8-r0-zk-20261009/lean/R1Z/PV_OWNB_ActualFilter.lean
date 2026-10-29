import R1Z.PV_OWNB_ActualSinkValid
import R1Z.PV_OWNB_CursorRead
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualFilter
open PV_OWNB_Cursor PV_OWN_Link PV_OWN_Bytes PV_OWNB_Padding
/-- Runtime writes may select different padding each time. This parameter is
an active-byte store law to discharge, never an allocator/runtime trust item. -/
def step (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor) : Cursor :=
 let next:=advance q
 if keep (q.source q.read) then
  PV_OWNB_ActualSink.sink next (q.source q.read) (bytes q.read (q.source q.read))
 else next

theorem valid (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor)
 (h:Valid q) (more:q.read<q.length)
 (copy:Agrees (PV_OWNB_LinkBytes.encode (q.source q.read)) (bytes q.read (q.source q.read))) :
 Valid (step keep bytes q) := by
 have ha:=PV_OWNB_CursorRead.advance q h more
 unfold step
 split
 · apply PV_OWNB_ActualSinkValid.valid _ _ _ ha _ copy
   unfold advance
   dsimp only
   unfold Valid at h
   exact Nat.lt_succ_of_le h.2.2.2.1
 · exact ha

theorem advances (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor) :
 (step keep bytes q).read=q.read+1 := by
 unfold step
 split <;> rfl

theorem source (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor) :
 (step keep bytes q).source=q.source := by
 unfold step
 split <;> rfl

attribute [local irreducible] step
#print axioms valid
#print axioms advances
#print axioms source
end R1Z.PV_OWNB_ActualFilter
