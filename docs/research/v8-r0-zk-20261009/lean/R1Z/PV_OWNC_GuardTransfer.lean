import R1Z.PV_OWNC_HeaderStores
set_option autoImplicit false
namespace R1Z.PV_OWNC_GuardTransfer
open PV_OWNB_Cursor PV_OWNC_GuardState PV_OWN_Heap PV_OWN_Operations
/-- Guard creation transfers responsibility for the original allocation,
not a second allocation or a fresh generation. -/
theorem owned (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (dst : Nat)
 (empty:q.memory.slots dst=none) (distinct:dst≠q.owner) :
 Owned (handoff q dst).memory dst q.token (handoff q dst).cell :=
 PV_OWNB_CursorTransfer.owned q h dst empty distinct

theorem source_consumed (q : Cursor) (dst : Nat) :
 (handoff q dst).memory.slots q.owner=none := by
 simp only [handoff,move,ite_true]

theorem identity (q : Cursor) (dst : Nat) :
 (handoff q dst).token=q.token ∧
 (handoff q dst).memory.generations=q.memory.generations ∧
 (handoff q dst).cell.contents=q.cell.contents := ⟨rfl,rfl,rfl⟩
#print axioms owned
#print axioms source_consumed
#print axioms identity
end R1Z.PV_OWNC_GuardTransfer
