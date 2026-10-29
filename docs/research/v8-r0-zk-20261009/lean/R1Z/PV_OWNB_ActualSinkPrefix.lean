import R1Z.PV_OWNB_ActualSink
import R1Z.PV_OWNB_RegionFrame
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualSinkPrefix
open PV_OWNB_Cursor PV_OWNB_LinkCodec
theorem frame (q : Cursor) (v : PV_OWN_Link.Link) (actual : PV_OWN_Bytes.Bytes) (h:Valid q)
 (i : Nat) (hi:i<q.written) : NativeView (PV_OWNB_ActualSink.sink q v actual).cell (i*8) (q.output i) := by
 unfold Valid at h
 unfold PV_OWNB_ActualSink.sink NativeView
 apply PV_OWNB_RegionFrame.disjoint
 · exact h.2.2.2.2.2.2.2 i hi
 · exact PV_OWNB_LinkBound.bounded (q.output i)
 · left; omega
#print axioms frame
end R1Z.PV_OWNB_ActualSinkPrefix
