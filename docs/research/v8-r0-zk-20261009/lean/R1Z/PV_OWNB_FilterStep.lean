import R1Z.PV_OWNB_CursorRead
import R1Z.PV_OWNB_SinkValid
set_option autoImplicit false
namespace R1Z.PV_OWNB_FilterStep
open PV_OWNB_Cursor PV_OWN_Link
/-- The value is read before branching; rejected POD values have no destructor call. -/
def step (keep : Link → Bool) (q : Cursor) : Cursor :=
 let next:=advance q
 if keep (q.source q.read) then sink next (q.source q.read) else next

theorem valid (keep : Link → Bool) (q : Cursor) (h:Valid q) (more:q.read<q.length) :
 Valid (step keep q) := by
 have ha:=PV_OWNB_CursorRead.advance q h more
 unfold step
 split
 · apply PV_OWNB_SinkValid.valid _ _ ha
   unfold advance
   unfold Valid at h
   exact Nat.lt_succ_of_le h.2.2.2.1
 · exact ha

theorem advances (keep : Link → Bool) (q : Cursor) : (step keep q).read=q.read+1 := by
 unfold step
 split <;> rfl

theorem generation (keep : Link → Bool) (q : Cursor) :
 (step keep q).token=q.token ∧ (step keep q).memory.generations=q.memory.generations := by
 unfold step
 split <;> exact ⟨rfl,rfl⟩
attribute [local irreducible] step
#print axioms valid
#print axioms advances
#print axioms generation
end R1Z.PV_OWNB_FilterStep
