import R1Z.PV_OWNC_SourceDetached
set_option autoImplicit false
namespace R1Z.PV_OWNC_GuardReturn
open PV_OWNB_Cursor PV_OWNC_GuardState PV_OWN_Heap
/-- mem::forget(dst_guard), then Vec::from_parts, transfers to the result slot.
The no-shrink selection means the original allocation is retained. -/
theorem returned_valid (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (dst : Nat)
 (empty:q.memory.slots dst=none) (distinct:dst≠q.owner) :
 PV_OWNB_Cursor.Valid (handoff q dst) ∧
 Owned (handoff q dst).memory dst q.token (handoff q dst).cell ∧
 (handoff q dst).memory.slots q.owner=none :=
 ⟨PV_OWNC_GuardValid.valid q h dst empty distinct,
 PV_OWNC_GuardTransfer.owned q h dst empty distinct,
 PV_OWNC_GuardTransfer.source_consumed q dst⟩

 theorem returned_header (q : Cursor) (dst : Nat) :
 (handoff q dst).capacity=q.capacity ∧ (handoff q dst).written=q.written ∧
 (handoff q dst).token.address=q.token.address := ⟨rfl,rfl,rfl⟩
#print axioms returned_valid
#print axioms returned_header
end R1Z.PV_OWNC_GuardReturn
