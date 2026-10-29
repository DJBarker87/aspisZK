import R1Z.PV_OWNC_PathPredicate
set_option autoImplicit false
namespace R1Z.PV_OWNC_CursorVector
open PV_OWNB_Cursor PV_OWNC_Vector PV_OWN_Link
/-- Vec::from_parts publishes the completed sink prefix with the original
capacity. All representations refer to the same byte cell. -/
def vector (q : Cursor) : Buffer Link :=
 ⟨q.memory,q.token,q.owner,q.cell,q.written,q.capacity,q.output⟩

theorem initialized (q : Cursor) (h:PV_OWNB_Cursor.Valid q) :
 PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec (vector q) := by
 unfold PV_OWNB_Cursor.Valid at h
 refine ⟨h.1,h.2.1,h.2.2.1,?_,?_⟩
 · change q.written≤q.capacity
   omega
 · exact h.2.2.2.2.2.2.2
#print axioms initialized
end R1Z.PV_OWNC_CursorVector
