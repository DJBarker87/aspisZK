import R1Z.PV_OWNB_ActualSink
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualSinkNew
open PV_OWNB_Cursor PV_OWNB_LinkCodec PV_OWN_Bytes PV_OWNB_Padding
theorem initialized (q : Cursor) (v : PV_OWN_Link.Link) (actual : Bytes) (h:Valid q)
 (room:q.written<q.read) (bytes:Agrees (PV_OWNB_LinkBytes.encode v) actual) :
 NativeView (PV_OWNB_ActualSink.sink q v actual).cell (q.written*8) v := by
 unfold Valid at h
 unfold PV_OWNB_ActualSink.sink NativeView
 apply PV_OWNB_PaddingStore.written
 · unfold Fits
   have hc:=h.2.1
   have hr:=h.2.2.2.2.1
   have hl:=h.2.2.2.2.2.1
   omega
 · exact PV_OWNB_LinkBound.bounded v
 · exact bytes
#print axioms initialized
end R1Z.PV_OWNB_ActualSinkNew
