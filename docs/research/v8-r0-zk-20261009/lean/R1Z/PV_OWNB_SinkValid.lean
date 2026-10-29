import R1Z.PV_OWNB_SinkOwnership
import R1Z.PV_OWNB_SinkNew
import R1Z.PV_OWNB_SinkUnread
import R1Z.PV_OWNB_SinkPrefix
set_option autoImplicit false
namespace R1Z.PV_OWNB_SinkValid
open PV_OWNB_Cursor PV_OWNB_LinkCodec
theorem valid (q : Cursor) (v : PV_OWN_Link.Link) (h:Valid q)
 (room:q.written<q.read) : Valid (sink q v) := by
 have own:=PV_OWNB_SinkOwnership.owned q v h
 have new:=PV_OWNB_SinkNew.initialized q v h room
 have unread:=PV_OWNB_SinkUnread.frame q v h room
 have old:=PV_OWNB_SinkPrefix.frame q v h
 unfold Valid at h ⊢
 refine ⟨own,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa [sink,PV_OWN_Bytes.store] using h.2.1
 · simpa [sink,PV_OWN_Bytes.store] using h.2.2.1
 · change q.written+1≤q.read; omega
 · exact h.2.2.2.2.1
 · exact h.2.2.2.2.2.1
 · exact unread
 · intro i hi
   change i<q.written+1 at hi
   by_cases he:i=q.written
   · subst i
     simpa [sink] using new
   · have hl:i<q.written := by omega
     simpa [sink,he] using old i hl
#print axioms valid
end R1Z.PV_OWNB_SinkValid
