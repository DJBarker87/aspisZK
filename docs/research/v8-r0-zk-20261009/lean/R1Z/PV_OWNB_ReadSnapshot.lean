import R1Z.PV_OWNB_CursorRead
set_option autoImplicit false
namespace R1Z.PV_OWNB_ReadSnapshot
open PV_OWNB_Cursor PV_OWNB_Padding PV_OWN_Bytes
/-- Optional bytes propagate padding without reading an uninitialized UInt8. -/
def bytes (q : Cursor) : Bytes := fun i=>q.cell.contents (q.read*8+i)

theorem represented (q : Cursor) (h:Valid q) (more:q.read<q.length) :
 Agrees (PV_OWNB_LinkBytes.encode (q.source q.read)) (bytes q) :=
 (PV_OWNB_CursorRead.read q h more).2
#print axioms represented
end R1Z.PV_OWNB_ReadSnapshot
