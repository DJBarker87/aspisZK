import R1Z.PV_OWN_Growth
import R1Z.PV_OWNC_Translation
set_option autoImplicit false
namespace R1Z.PV_OWNC_LinkGrowth
open PV_OWN_Heap PV_OWN_Bytes PV_OWNB_LinkCodec
/-- Reallocation preserves arbitrary Link padding. Active bytes and bounds
are transported from old storage; no inactive byte is required initialized. -/
theorem represented (c : Cell) (newSize cap s : Nat) (v : PV_OWN_Link.Link)
 (h:NativeView c s v) (grow:c.size≤newSize) :
 NativeView (PV_OWN_Growth.grownCell c newSize cap) s v := by
 refine ⟨Nat.le_trans h.1 grow,?_⟩
 intro i z hi
 have bound:=PV_OWNB_LinkBound.bounded v i z hi
 have inside:s+i<c.size := by have hh:=h.1;unfold Fits at hh;omega
 rw [PV_OWN_Growth.prefix_bytes c newSize cap (s+i) inside]
 exact h.2 i z hi
#print axioms represented
end R1Z.PV_OWNC_LinkGrowth
