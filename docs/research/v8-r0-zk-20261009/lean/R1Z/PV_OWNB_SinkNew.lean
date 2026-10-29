import R1Z.PV_OWNB_Cursor
set_option autoImplicit false
namespace R1Z.PV_OWNB_SinkNew
open PV_OWNB_Cursor PV_OWNB_LinkCodec PV_OWN_Bytes
theorem initialized (q : Cursor) (v : PV_OWN_Link.Link) (h:Valid q)
 (room:q.written<q.read) : NativeView (sink q v).cell (q.written*8) v := by
 unfold Valid at h
 unfold sink NativeView
 apply PV_OWNB_PaddingStore.canonical
 · unfold Fits
   have hc:=h.2.1
   have hr:=h.2.2.2.2.1
   have hl:=h.2.2.2.2.2.1
   omega
 · exact PV_OWNB_LinkBound.bounded v
#print axioms initialized
end R1Z.PV_OWNB_SinkNew
