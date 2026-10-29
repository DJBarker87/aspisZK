import R1Z.PV_OWNC_Specialization
import R1Z.PV_OWNB_CursorTransfer
import R1Z.PV_OWNB_CursorExit
set_option autoImplicit false
namespace R1Z.PV_OWNC_GuardState
open PV_OWNB_Cursor PV_OWNC_SourceIterator
/-- Header stores from forget_allocation_drop_remaining, in source order.
The incoming remaining-slice snapshot must be saved before these stores. -/
def clearCap (h : Header) : Header := {h with cap:=0}
def clearBuf (h : Header) : Header := {h with buf:=2}
def clearPtr (h : Header) : Header := {h with ptr:=h.buf}
def clearEnd (h : Header) : Header := {h with endPtr:=h.buf}
def reset (h : Header) : Header := clearEnd (clearPtr (clearBuf (clearCap h)))
def remaining (h : Header) : Nat × Nat := (h.ptr,(h.endPtr-h.ptr)/8)

/-- Same live generation, bytes and cursor fields with an explicitly moved
owner. This is the temporary destination-data/source-buffer guard. -/
def handoff (q : Cursor) (dst : Nat) : Cursor :=
 {q with owner:=dst,cell:={q.cell with owner:=dst},
  memory:=PV_OWN_Operations.move q.owner dst q.token q.cell q.memory}
end R1Z.PV_OWNC_GuardState
