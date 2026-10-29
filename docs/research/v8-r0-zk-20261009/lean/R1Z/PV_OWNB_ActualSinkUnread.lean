import R1Z.PV_OWNB_ActualSink
import R1Z.PV_OWNB_RegionFrame
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualSinkUnread
open PV_OWNB_Cursor PV_OWNB_LinkCodec
theorem frame (q : Cursor) (v : PV_OWN_Link.Link) (actual : PV_OWN_Bytes.Bytes) (h:Valid q)
 (room:q.written<q.read) (i : Nat) (lo:q.read≤i) (hi:i<q.length) :
 NativeView (PV_OWNB_ActualSink.sink q v actual).cell (i*8) (q.source i) := by
 unfold Valid at h
 unfold PV_OWNB_ActualSink.sink NativeView
 apply PV_OWNB_RegionFrame.disjoint
 · exact h.2.2.2.2.2.2.1 i lo hi
 · exact PV_OWNB_LinkBound.bounded (q.source i)
 · right; omega
#print axioms frame
end R1Z.PV_OWNB_ActualSinkUnread
