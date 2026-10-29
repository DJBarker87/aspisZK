import R1Z.PV_OWNB_Cursor
import R1Z.PV_OWN_CheckedMove
set_option autoImplicit false
namespace R1Z.PV_OWNB_CursorTransfer
open PV_OWNB_Cursor PV_OWN_Heap PV_OWN_Operations
/-- The allocation is transferred exactly once after the source scope is disarmed. -/
def command (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (dst : Nat) (empty:q.memory.slots dst=none)
 (distinct:dst≠q.owner) : PV_OWN_CheckedMove.Command q.memory :=
 ⟨q.token,q.cell,q.owner,dst,h.1.1,h.1.2,empty,distinct⟩

theorem owned (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (dst : Nat) (empty:q.memory.slots dst=none)
 (distinct:dst≠q.owner) :
 Owned (PV_OWN_CheckedMove.execute (command q h dst empty distinct)) dst q.token {q.cell with owner:=dst} :=
 PV_OWN_CheckedMove.transferred _

theorem source_consumed (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (dst : Nat) (empty:q.memory.slots dst=none)
 (distinct:dst≠q.owner) :
 (PV_OWN_CheckedMove.execute (command q h dst empty distinct)).slots q.owner=none :=
 PV_OWN_CheckedMove.source_consumed _
#print axioms owned
#print axioms source_consumed
end R1Z.PV_OWNB_CursorTransfer
