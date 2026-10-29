import R1Z.PV_OWNB_ActualSink
import R1Z.PV_OWNB_ActualSinkNew
import R1Z.PV_OWNB_ActualSinkUnread
import R1Z.PV_OWNB_ActualSinkPrefix
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualSinkValid
open PV_OWNB_Cursor PV_OWNB_LinkCodec
theorem valid (q : Cursor) (v : PV_OWN_Link.Link) (actual : PV_OWN_Bytes.Bytes) (h:Valid q)
 (room:q.written<q.read) (bytes:PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) actual) : Valid (PV_OWNB_ActualSink.sink q v actual) := by
 have own:=PV_OWNB_ActualSink.ownership q v actual h
 have new:=PV_OWNB_ActualSinkNew.initialized q v actual h room bytes
 have unread:=PV_OWNB_ActualSinkUnread.frame q v actual h room
 have old:=PV_OWNB_ActualSinkPrefix.frame q v actual h
 unfold Valid at h ⊢
 refine ⟨own,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa [PV_OWNB_ActualSink.sink,PV_OWN_Bytes.store] using h.2.1
 · simpa [PV_OWNB_ActualSink.sink,PV_OWN_Bytes.store] using h.2.2.1
 · change q.written+1≤q.read; omega
 · exact h.2.2.2.2.1
 · exact h.2.2.2.2.2.1
 · exact unread
 · intro i hi
   change i<q.written+1 at hi
   by_cases he:i=q.written
   · subst i
     simpa [PV_OWNB_ActualSink.sink] using new
   · have hl:i<q.written := by omega
     simpa [PV_OWNB_ActualSink.sink,he] using old i hl
#print axioms valid
end R1Z.PV_OWNB_ActualSinkValid
